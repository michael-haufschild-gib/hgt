import Mathlib

/-!
# Rank-one orientation and Lorentzianization

A one-dimensional absolute quotient of a two-term complex, and the inertia of a positive form
perturbed by the square of a single linear port.

The first section proves that a splitting datum `D H + j T = 1`, `T D = 0`, `T j = 1` makes the
range of `D` a complement of the range of `j`, identifies the quotient with the absolute object,
and decomposes every linear observer into an absolute and a relative part.

The second section proves that adding `Γ · M(x)²` to a positive definite form on a
finite-dimensional real inner product space can create at most one nonpositive direction: every
subspace on which the perturbed form is nonpositive has dimension at most one.  The sign of the
port is then erased by a unique orthogonal reflection.

The last two sections record the two boundaries: a reciprocal one-parameter flow admits no nonzero
invariant positive semidefinite quadratic form, and with two independent ports the rank-one
conclusion fails.
-/

namespace HTGeometry.ConstraintRelativity

open scoped InnerProductSpace

/-! ## The absolute source quotient -/

section AbsoluteQuotient

variable {R A₁ A₂ O : Type*} [CommRing R]
  [AddCommGroup A₁] [Module R A₁] [AddCommGroup A₂] [Module R A₂] [AddCommGroup O] [Module R O]

/-- A splitting datum for `A₁ → A₂ → O`: `D H + j T = 1`, `T D = 0`, `T j = 1`. -/
structure IsAbsoluteSplitting (D : A₁ →ₗ[R] A₂) (T : A₂ →ₗ[R] O)
    (H : A₂ →ₗ[R] A₁) (jm : O →ₗ[R] A₂) : Prop where
  splitting : ∀ x, D (H x) + jm (T x) = x
  comp_TD : ∀ y, T (D y) = 0
  comp_Tj : ∀ o, T (jm o) = o

variable {D : A₁ →ₗ[R] A₂} {T : A₂ →ₗ[R] O} {H : A₂ →ₗ[R] A₁} {jm : O →ₗ[R] A₂}

/-- The relative and absolute ranges are complementary: `A₂ = im D ⊕ j(O)`. -/
theorem IsAbsoluteSplitting.isCompl (h : IsAbsoluteSplitting D T H jm) :
    IsCompl (LinearMap.range D) (LinearMap.range jm) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro x ⟨y, rfl⟩ ⟨o, ho⟩
    have hzero : o = 0 := by rw [← h.comp_Tj o, ho, h.comp_TD]
    rw [← ho, hzero, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx := h.splitting x
    exact hx ▸ Submodule.add_mem_sup ⟨H x, rfl⟩ ⟨T x, rfl⟩

theorem IsAbsoluteSplitting.range_le_ker (h : IsAbsoluteSplitting D T H jm) :
    LinearMap.range D ≤ LinearMap.ker T := by
  rintro x ⟨y, rfl⟩
  simp [LinearMap.mem_ker, h.comp_TD]

/-- The absolute quotient: `A₂ / im D ≅ O`, with inverse induced by the section `j`. -/
noncomputable def IsAbsoluteSplitting.quotEquiv (h : IsAbsoluteSplitting D T H jm) :
    (A₂ ⧸ LinearMap.range D) ≃ₗ[R] O :=
  LinearEquiv.ofLinear (Submodule.liftQ _ T h.range_le_ker)
    ((LinearMap.range D).mkQ.comp jm)
    (by ext o; simp [h.comp_Tj])
    (by
      refine Submodule.linearMap_qext _ ?_
      ext a
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
        LinearMap.id_comp]
      rw [Submodule.Quotient.eq]
      refine ⟨-(H a), ?_⟩
      have ha := h.splitting a
      simp only [map_neg]
      linear_combination (norm := module) -ha)

@[simp]
theorem IsAbsoluteSplitting.quotEquiv_mk (h : IsAbsoluteSplitting D T H jm) (a : A₂) :
    h.quotEquiv (Submodule.Quotient.mk a) = T a := rfl

variable {W : Type*} [AddCommGroup W] [Module R W]

/-- Every linear observer splits as an absolute part read through `T` and a relative part read
through `D`. -/
theorem IsAbsoluteSplitting.observer_decomp (h : IsAbsoluteSplitting D T H jm)
    (F : A₂ →ₗ[R] W) : F = (F.comp jm).comp T + (F.comp D).comp H := by
  ext x
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  rw [← map_add, add_comm (jm (T x)) (D (H x)), h.splitting x]

/-- A boundary-blind observer factors through the one-dimensional absolute coordinate. -/
theorem IsAbsoluteSplitting.observer_factors (h : IsAbsoluteSplitting D T H jm)
    {F : A₂ →ₗ[R] W} (hF : F.comp D = 0) : F = (F.comp jm).comp T := by
  ext x
  have hdec := congrArg (fun f => f x) (h.observer_decomp F)
  have h0 : F (D (H x)) = 0 := congrArg (fun f => f (H x)) hF
  simp only [LinearMap.add_apply, LinearMap.comp_apply] at hdec ⊢
  rw [hdec, h0, add_zero]

/-- The factorization through `T` is unique, because `T` is surjective. -/
theorem IsAbsoluteSplitting.factor_unique (h : IsAbsoluteSplitting D T H jm)
    {G G' : O →ₗ[R] W} (hEq : G.comp T = G'.comp T) : G = G' := by
  ext o
  have := congrArg (fun f => f (jm o)) hEq
  simpa [h.comp_Tj] using this

/-- **The splitting datum exists.**  For every relative module `A₁` and every observer module `O`
the product carries a canonical absolute splitting, with `D` the inclusion, `T` the projection,
`H` the retraction and `j` the section.  The theorems above are therefore not vacuous. -/
theorem isAbsoluteSplitting_prod (A₁ O : Type*) [AddCommGroup A₁] [Module R A₁]
    [AddCommGroup O] [Module R O] :
    IsAbsoluteSplitting (R := R) (LinearMap.inl R A₁ O) (LinearMap.snd R A₁ O)
      (LinearMap.fst R A₁ O) (LinearMap.inr R A₁ O) where
  splitting x := by
    refine Prod.ext ?_ ?_
    · show x.1 + 0 = x.1
      rw [add_zero]
    · show (0 : O) + x.2 = x.2
      rw [zero_add]
  comp_TD _ := rfl
  comp_Tj _ := rfl

/-- The canonical splitting has nonzero absolute part whenever the observer module is nonzero, so
the absolute quotient of a splitting datum is not forced to vanish. -/
theorem isAbsoluteSplitting_prod_observer_ne_bot (A₁ O : Type*) [AddCommGroup A₁] [Module R A₁]
    [AddCommGroup O] [Module R O] [Nontrivial O] :
    LinearMap.range (LinearMap.inr R A₁ O) ≠ ⊥ := by
  obtain ⟨o, ho⟩ := exists_ne (0 : O)
  intro hbot
  refine ho ?_
  have hmem : LinearMap.inr R A₁ O o ∈ LinearMap.range (LinearMap.inr R A₁ O) := ⟨o, rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact congrArg Prod.snd hmem

end AbsoluteQuotient

/-! ## Coframe before metric: rank-one Lorentzianization -/

section RankOneInertia

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The Riesz vector of a linear port. -/
noncomputable def portVector (M : V →ₗ[ℝ] ℝ) : V :=
  (InnerProductSpace.toDual ℝ V).symm (LinearMap.toContinuousLinearMap M)

@[simp]
theorem inner_portVector (M : V →ₗ[ℝ] ℝ) (x : V) : ⟪portVector M, x⟫_ℝ = M x := by
  rw [portVector, InnerProductSpace.toDual_symm_apply]
  rfl

theorem portVector_ne_zero {M : V →ₗ[ℝ] ℝ} (hM : M ≠ 0) : portVector M ≠ 0 := by
  intro h
  refine hM (LinearMap.ext fun x => ?_)
  rw [← inner_portVector M x, h, inner_zero_left, LinearMap.zero_apply]

/-- The port scale `c = M(r) = ⟪r,r⟫`. -/
noncomputable def portScale (M : V →ₗ[ℝ] ℝ) : ℝ := M (portVector M)

theorem portScale_pos {M : V →ₗ[ℝ] ℝ} (hM : M ≠ 0) : 0 < portScale M := by
  rw [portScale, ← inner_portVector M (portVector M)]
  exact real_inner_self_pos.2 (portVector_ne_zero hM)

/-- The normalized port axis `u = r / c`, characterized by `M(u) = 1`. -/
noncomputable def portAxis (M : V →ₗ[ℝ] ℝ) : V := (portScale M)⁻¹ • portVector M

@[simp]
theorem map_portAxis {M : V →ₗ[ℝ] ℝ} (hM : M ≠ 0) : M (portAxis M) = 1 := by
  rw [portAxis, map_smul, smul_eq_mul, ← portScale]
  exact inv_mul_cancel₀ (portScale_pos hM).ne'

theorem inner_portAxis_right (M : V →ₗ[ℝ] ℝ) (x : V) :
    ⟪x, portAxis M⟫_ℝ = (portScale M)⁻¹ * M x := by
  rw [portAxis, real_inner_smul_right, real_inner_comm, inner_portVector]

theorem inner_portAxis_left (M : V →ₗ[ℝ] ℝ) (x : V) :
    ⟪portAxis M, x⟫_ℝ = (portScale M)⁻¹ * M x := by
  rw [real_inner_comm, inner_portAxis_right]

theorem inner_portAxis_self {M : V →ₗ[ℝ] ℝ} (hM : M ≠ 0) :
    ⟪portAxis M, portAxis M⟫_ℝ = (portScale M)⁻¹ := by
  rw [inner_portAxis_right, map_portAxis hM, mul_one]

/-- The transverse part `z = x − M(x)·u` lies in `ker M` and is orthogonal to the axis. -/
theorem map_transverse {M : V →ₗ[ℝ] ℝ} (hM : M ≠ 0) (x : V) :
    M (x - M x • portAxis M) = 0 := by
  simp [map_portAxis hM]

theorem inner_transverse_portAxis {M : V →ₗ[ℝ] ℝ} (hM : M ≠ 0) (x : V) :
    ⟪x - M x • portAxis M, portAxis M⟫_ℝ = 0 := by
  rw [inner_sub_left, real_inner_smul_left, inner_portAxis_right, inner_portAxis_self hM]
  ring

/-- The perturbed quadratic form `Q(x) = ⟪x,x⟫ + Γ·M(x)²`. -/
noncomputable def portForm (M : V →ₗ[ℝ] ℝ) (Γ : ℝ) (x : V) : ℝ := ⟪x, x⟫_ℝ + Γ * (M x) ^ (2 : ℕ)

/-- The coefficient of the port direction after diagonalization: `Ω = c⁻¹ + Γ`. -/
noncomputable def portOmega (M : V →ₗ[ℝ] ℝ) (Γ : ℝ) : ℝ := (portScale M)⁻¹ + Γ

/-- **Rank-one Lorentzianization.**  In the orthogonal splitting `x = z + M(x)·u` the perturbed
form is the positive transverse form plus `Ω·M(x)²`. -/
theorem portForm_eq {M : V →ₗ[ℝ] ℝ} (hM : M ≠ 0) (Γ : ℝ) (x : V) :
    portForm M Γ x
      = ⟪x - M x • portAxis M, x - M x • portAxis M⟫_ℝ + portOmega M Γ * (M x) ^ (2 : ℕ) := by
  have hexp : ⟪x - M x • portAxis M, x - M x • portAxis M⟫_ℝ
      = ⟪x, x⟫_ℝ - (portScale M)⁻¹ * (M x) ^ (2 : ℕ) := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      inner_portAxis_right, inner_portAxis_left, map_smul, smul_eq_mul, map_portAxis hM]
    ring
  rw [hexp, portForm, portOmega]
  ring

omit [FiniteDimensional ℝ V] in
/-- The transverse form is positive definite: on `ker M` the perturbation is invisible. -/
theorem portForm_pos_of_map_eq_zero (M : V →ₗ[ℝ] ℝ) (Γ : ℝ) {x : V} (hx : M x = 0)
    (hx0 : x ≠ 0) : 0 < portForm M Γ x := by
  rw [portForm, hx]
  simpa using real_inner_self_pos.2 hx0

omit [FiniteDimensional ℝ V] in
/-- **The rank-one inertia bound.**  Every subspace on which the perturbed form is nonpositive is
at most one-dimensional: `ind₋(Q) + dim Rad(Q) ≤ 1`. -/
theorem finrank_le_one_of_portForm_nonpos (M : V →ₗ[ℝ] ℝ) (Γ : ℝ) (W : Submodule ℝ V)
    (hW : ∀ x ∈ W, portForm M Γ x ≤ 0) : Module.finrank ℝ W ≤ 1 := by
  have hinj : Function.Injective (M.comp W.subtype) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hx⟩ hker
    have hMx : M x = 0 := hker
    rw [Submodule.mem_bot, Submodule.mk_eq_zero]
    by_contra hx0
    exact absurd (hW x hx) (not_le.2 (portForm_pos_of_map_eq_zero M Γ hMx hx0))
  simpa using (M.comp W.subtype).finrank_le_finrank_of_injective hinj

/-- Positive phase `Ω > 0`: the perturbed form is positive definite. -/
theorem portForm_pos_of_omega_pos {M : V →ₗ[ℝ] ℝ} (hM : M ≠ 0) {Γ : ℝ}
    (hΩ : 0 < portOmega M Γ) {x : V} (hx : x ≠ 0) : 0 < portForm M Γ x := by
  rw [portForm_eq hM]
  rcases eq_or_ne (M x) 0 with h | h
  · have hz : x - M x • portAxis M = x := by simp [h]
    rw [hz, h]
    simpa using real_inner_self_pos.2 hx
  · have h1 : 0 ≤ ⟪x - M x • portAxis M, x - M x • portAxis M⟫_ℝ := real_inner_self_nonneg
    have hsq : 0 < (M x) ^ (2 : ℕ) := by
      rcases lt_trichotomy (M x) 0 with h' | h' | h'
      · nlinarith
      · exact absurd h' h
      · nlinarith
    have h2 : 0 < portOmega M Γ * (M x) ^ (2 : ℕ) := mul_pos hΩ hsq
    linarith

/-- Null phase `Ω = 0`: the radical of the perturbed form is exactly the port axis. -/
theorem portForm_eq_zero_iff_of_omega_zero {M : V →ₗ[ℝ] ℝ} (hM : M ≠ 0) {Γ : ℝ}
    (hΩ : portOmega M Γ = 0) (x : V) :
    portForm M Γ x = 0 ↔ x ∈ Submodule.span ℝ {portAxis M} := by
  rw [portForm_eq hM, hΩ, zero_mul, add_zero]
  constructor
  · intro h
    have : x - M x • portAxis M = 0 := by
      simpa using (inner_self_eq_zero (𝕜 := ℝ)).1 h
    exact Submodule.mem_span_singleton.2 ⟨M x, by linear_combination (norm := module) -this⟩
  · intro h
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 h
    rw [map_smul, smul_eq_mul, map_portAxis hM, mul_one, sub_self]
    simp

/-- Lorentz phase `Ω < 0`: the port axis is a timelike direction. -/
theorem portForm_portAxis {M : V →ₗ[ℝ] ℝ} (hM : M ≠ 0) (Γ : ℝ) :
    portForm M Γ (portAxis M) = portOmega M Γ := by
  rw [portForm_eq hM, map_portAxis hM, one_smul, sub_self]
  simp

omit [FiniteDimensional ℝ V] in
/-- In the Lorentz phase the timelike set misses the kernel of the port: the two time cones are
separated by the sign of `M`. -/
theorem map_ne_zero_of_portForm_neg (M : V →ₗ[ℝ] ℝ) (Γ : ℝ) {x : V}
    (hx : portForm M Γ x < 0) : M x ≠ 0 := by
  intro h
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [portForm] at hx
  · exact absurd hx (not_lt.2 (portForm_pos_of_map_eq_zero M Γ h hx0).le)

/-! ## Time reversal and orientation erasure -/

/-- The port reflection `Θ(z + t u) = z − t u`. -/
noncomputable def portReflect (M : V →ₗ[ℝ] ℝ) (x : V) : V := x - (2 * M x) • portAxis M

@[simp]
theorem map_portReflect {M : V →ₗ[ℝ] ℝ} (hM : M ≠ 0) (x : V) :
    M (portReflect M x) = - M x := by
  simp only [portReflect, map_sub, map_smul, smul_eq_mul, map_portAxis hM, mul_one]
  ring

theorem portReflect_of_map_eq_zero (M : V →ₗ[ℝ] ℝ) {x : V} (hx : M x = 0) :
    portReflect M x = x := by
  simp [portReflect, hx]

@[simp]
theorem portReflect_portAxis {M : V →ₗ[ℝ] ℝ} (hM : M ≠ 0) :
    portReflect M (portAxis M) = - portAxis M := by
  rw [portReflect, map_portAxis hM]
  module

theorem portReflect_involutive {M : V →ₗ[ℝ] ℝ} (hM : M ≠ 0) (x : V) :
    portReflect M (portReflect M x) = x := by
  simp only [portReflect, map_sub, map_smul, smul_eq_mul, map_portAxis hM, mul_one]
  module

/-- The port reflection is an isometry for the positive form. -/
theorem inner_portReflect {M : V →ₗ[ℝ] ℝ} (hM : M ≠ 0) (x y : V) :
    ⟪portReflect M x, portReflect M y⟫_ℝ = ⟪x, y⟫_ℝ := by
  simp only [portReflect, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, inner_portAxis_right, inner_portAxis_left, map_smul, smul_eq_mul,
    map_portAxis hM]
  ring

/-- The port reflection preserves the perturbed form. -/
theorem portForm_portReflect {M : V →ₗ[ℝ] ℝ} (hM : M ≠ 0) (Γ : ℝ) (x : V) :
    portForm M Γ (portReflect M x) = portForm M Γ x := by
  rw [portForm, portForm, inner_portReflect hM, map_portReflect hM]
  ring

/-- **Uniqueness of the port reflection.**  Any orthogonal map fixing `ker M` pointwise and
negating `M` is `Θ`. -/
theorem eq_portReflect {M : V →ₗ[ℝ] ℝ} (hM : M ≠ 0) (S : V →ₗ[ℝ] V)
    (hker : ∀ x, M x = 0 → S x = x) (hneg : ∀ x, M (S x) = - M x)
    (hiso : ∀ x y, ⟪S x, S y⟫_ℝ = ⟪x, y⟫_ℝ) (x : V) : S x = portReflect M x := by
  have hSu : S (portAxis M) = - portAxis M := by
    set w := S (portAxis M) + portAxis M with hw
    have hwker : M w = 0 := by
      rw [hw, map_add, hneg, map_portAxis hM]; ring
    have hperp : ∀ z, M z = 0 → ⟪w, z⟫_ℝ = 0 := by
      intro z hz
      have h2 : ⟪portAxis M, z⟫_ℝ = 0 := by
        rw [real_inner_comm, inner_portAxis_right, hz, mul_zero]
      have h1 : ⟪S (portAxis M), z⟫_ℝ = 0 := by
        rw [← hker z hz, hiso]
        exact h2
      rw [hw, inner_add_left, h1, h2, add_zero]
    have : ⟪w, w⟫_ℝ = 0 := hperp w hwker
    have hw0 : w = 0 := (inner_self_eq_zero (𝕜 := ℝ)).1 this
    rw [hw] at hw0
    linear_combination (norm := module) hw0
  have hx : S x = S (x - M x • portAxis M) + S (M x • portAxis M) := by
    rw [← map_add]; congr 1; module
  rw [hx, hker _ (map_transverse hM x), map_smul, hSu]
  simp only [portReflect]
  module

/-- Every reader built from the transverse form, the squared port, or the perturbed form is
reflection invariant, hence blind to the sign of the port. -/
theorem sq_map_portReflect {M : V →ₗ[ℝ] ℝ} (hM : M ≠ 0) (x : V) :
    (M (portReflect M x)) ^ (2 : ℕ) = (M x) ^ (2 : ℕ) := by
  rw [map_portReflect hM]; ring

/-- Positivity alone does not erase orientation: `exp ∘ M` is positive and separates `x` from its
reflection whenever the port is nonzero. -/
theorem exp_map_portReflect_ne {M : V →ₗ[ℝ] ℝ} (hM : M ≠ 0) {x : V} (hx : M x ≠ 0) :
    Real.exp (M (portReflect M x)) ≠ Real.exp (M x) := by
  rw [map_portReflect hM, ne_eq, Real.exp_eq_exp]
  intro h
  exact hx (by linarith)

end RankOneInertia

/-! ## The reciprocal-flow no-go -/

section ReciprocalFlow

/-- A general binary quadratic form. -/
noncomputable def binQuad (A B D a b : ℝ) : ℝ := A * a ^ (2 : ℕ) + 2 * B * (a * b) + D * b ^ (2 : ℕ)

/-- **The reciprocal invariance no-go, diagonal part.**  A quadratic form invariant under the
reciprocal flow `(a,b) ↦ (e^{sμ}a, e^{−sμ}b)` has no diagonal terms. -/
theorem binQuad_diag_eq_zero {μ A B D : ℝ} (hμ : μ ≠ 0)
    (h : ∀ s a b : ℝ, binQuad A B D (Real.exp (s * μ) * a) (Real.exp (-(s * μ)) * b)
      = binQuad A B D a b) : A = 0 ∧ D = 0 := by
  have hexp : Real.exp (1 * μ) ^ (2 : ℕ) ≠ 1 := by
    intro hcon
    have hpos : (0:ℝ) < Real.exp (1 * μ) := Real.exp_pos _
    have : Real.exp (1 * μ) = 1 := by
      nlinarith [hcon, hpos]
    rw [Real.exp_eq_one_iff] at this
    exact hμ (by linarith)
  constructor
  · have := h 1 1 0
    simp only [binQuad, mul_zero, mul_one, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true] at this
    have h2 : A * (Real.exp (1 * μ) ^ (2 : ℕ) - 1) = 0 := by nlinarith [this]
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exact absurd (by linarith : Real.exp (1 * μ) ^ (2 : ℕ) = 1) hexp
  · have := h 1 0 1
    simp only [binQuad, mul_zero, mul_one, zero_mul, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true] at this
    have hne : Real.exp (-(1 * μ)) ^ (2 : ℕ) - 1 ≠ 0 := by
      intro hcon
      apply hexp
      have hmul : Real.exp (1 * μ) * Real.exp (-(1 * μ)) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [hmul, hcon, Real.exp_pos (1 * μ), Real.exp_pos (-(1 * μ))]
    have h2 : D * (Real.exp (-(1 * μ)) ^ (2 : ℕ) - 1) = 0 := by nlinarith [this]
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exact absurd h3 hne

/-- **The reciprocal invariance no-go.**  A positive semidefinite quadratic form invariant under
the reciprocal flow is zero: no nonzero positive energy is both complete and invariant. -/
theorem binQuad_eq_zero_of_nonneg {μ A B D : ℝ} (hμ : μ ≠ 0)
    (h : ∀ s a b : ℝ, binQuad A B D (Real.exp (s * μ) * a) (Real.exp (-(s * μ)) * b)
      = binQuad A B D a b)
    (hpos : ∀ a b : ℝ, 0 ≤ binQuad A B D a b) : ∀ a b : ℝ, binQuad A B D a b = 0 := by
  obtain ⟨hA, hD⟩ := binQuad_diag_eq_zero hμ h
  have hB : B = 0 := by
    have h1 := hpos 1 1
    have h2 := hpos 1 (-1)
    simp only [binQuad, hA, hD] at h1 h2
    nlinarith [h1, h2]
  intro a b
  simp [binQuad, hA, hD, hB]

end ReciprocalFlow

/-! ## The two-port countermodel -/

section TwoPortCountermodel

/-- With two independent ports the rank-one conclusion fails: `P − 2M₁² − 2M₂²` is negative
definite on a two-dimensional space. -/
theorem two_port_negative_definite (x : Fin 2 → ℝ) :
    ((x 0) ^ (2 : ℕ) + (x 1) ^ (2 : ℕ)) - 2 * (x 0) ^ (2 : ℕ) - 2 * (x 1) ^ (2 : ℕ) = -((x 0) ^ (2 : ℕ) + (x 1) ^ (2 : ℕ)) := by
  ring

/-- The nonpositive locus of the two-port form is all of a two-dimensional space, so the rank-one
inertia bound is genuinely a one-port statement. -/
theorem two_port_nonpos (x : Fin 2 → ℝ) :
    ((x 0) ^ (2 : ℕ) + (x 1) ^ (2 : ℕ)) - 2 * (x 0) ^ (2 : ℕ) - 2 * (x 1) ^ (2 : ℕ) ≤ 0 := by
  rw [two_port_negative_definite]
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

end TwoPortCountermodel

end HTGeometry.ConstraintRelativity
