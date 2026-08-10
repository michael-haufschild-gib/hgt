import Mathlib

/-!
# Conormal persistence and the bounded-dilation no-go

A decreasing filtration of closed subspaces of a normed space carries an exact persistence row of
boundary defects, and the quotient distance to a member of the filtration is computed by the unit
ball of its annihilator.  An isometric flow rescaling the filtration parameter therefore preserves
the quotient distance exactly.

The scaling relation `V P V* = c·P` with `V` unitary and `c ≠ 1` forces `P = 0` for bounded `P`,
with an explicit lower bound on the relative defect; the same relation on an unbounded operator
makes every moment grow geometrically, so no orbit recurs.
-/

open Metric

namespace HTGeometry.ConstraintRelativity

/-! ## The persistence row of a nested pair -/

section Persistence

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- The boundary defect of a subspace. -/
abbrev boundaryDefect (N : Submodule R E) : Type _ := E ⧸ N

/-- The comparison map of a nested pair of subspaces. -/
noncomputable def persistenceMap {A B : Submodule R E} (h : B ≤ A) :
    boundaryDefect B →ₗ[R] boundaryDefect A :=
  Submodule.mapQ B A LinearMap.id h

@[simp] theorem persistenceMap_mk {A B : Submodule R E} (h : B ≤ A) (x : E) :
    persistenceMap h (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

theorem persistenceMap_surjective {A B : Submodule R E} (h : B ≤ A) :
    Function.Surjective (persistenceMap h) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- **Card `(4)`, exactness at the middle.**  The kernel of the comparison map is the intermediate
layer `M(a)/M(b)`. -/
theorem ker_persistenceMap {A B : Submodule R E} (h : B ≤ A) :
    LinearMap.ker (persistenceMap h) = Submodule.map B.mkQ A := by
  ext y
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    constructor
    · intro hx
      have hxA : x ∈ A := by
        have : (Submodule.Quotient.mk x : boundaryDefect A) = 0 := hx
        exact (Submodule.Quotient.mk_eq_zero A).1 this
      exact ⟨x, hxA, rfl⟩
    · rintro ⟨z, hz, hzx⟩
      have hxz : x - z ∈ B := (Submodule.Quotient.eq B).1 hzx.symm
      have : x ∈ A := by
        have := A.add_mem hz (h hxz)
        simpa using this
      show (Submodule.Quotient.mk x : boundaryDefect A) = 0
      exact (Submodule.Quotient.mk_eq_zero A).2 this

/-- **Card `(4)`, exactness at the left.**  The intermediate layer injects into the larger boundary
defect. -/
theorem injective_inclusion_layer {A B : Submodule R E} (_h : B ≤ A) :
    Function.Injective ((Submodule.map B.mkQ A).subtype) :=
  Submodule.injective_subtype _

end Persistence

/-! ## Quotient distance and its annihilator duality -/

section QuotientDistance

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Card `(6)`.**  The quotient distance to a subspace. -/
noncomputable def quotientDistance (N : Submodule 𝕜 E) (x : E) : ℝ := infDist x N

theorem norm_quotient_mk (N : Submodule 𝕜 E) (x : E) :
    ‖(Submodule.Quotient.mk x : E ⧸ N)‖ = quotientDistance N x :=
  QuotientAddGroup.norm_mk _

/-- The annihilator of a subspace inside the dual. -/
def conormal (N : Submodule 𝕜 E) : Set (StrongDual 𝕜 E) :=
  {f | ∀ y ∈ N, f y = 0}

/-- **Card `(7)`, upper bound.**  Every unit annihilator functional is bounded by the quotient
distance. -/
theorem norm_le_quotientDistance {N : Submodule 𝕜 E} {f : StrongDual 𝕜 E} (hf : f ∈ conormal N)
    (hf1 : ‖f‖ ≤ 1) (x : E) : ‖f x‖ ≤ quotientDistance N x := by
  refine (le_infDist ⟨0, N.zero_mem⟩).2 ?_
  rintro y hy
  · have hxy : f x = f (x - y) := by
      rw [map_sub, hf y hy, sub_zero]
    calc ‖f x‖ = ‖f (x - y)‖ := by rw [hxy]
      _ ≤ ‖f‖ * ‖x - y‖ := f.le_opNorm _
      _ ≤ 1 * ‖x - y‖ := by
          exact mul_le_mul_of_nonneg_right hf1 (norm_nonneg _)
      _ = dist x y := by rw [one_mul, dist_eq_norm]

end QuotientDistance

/-! ## Hahn-Banach: the quotient distance is attained on the conormal unit ball -/

section Duality

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The quotient map as a norm-nonincreasing continuous linear map. -/
noncomputable def quotientCLM (N : Submodule 𝕜 E) : E →L[𝕜] E ⧸ N :=
  LinearMap.mkContinuous N.mkQ 1 fun x => by
    simpa using Submodule.Quotient.norm_mk_le (S := N) x

@[simp] theorem quotientCLM_apply (N : Submodule 𝕜 E) (x : E) :
    quotientCLM N x = Submodule.Quotient.mk x := rfl

theorem norm_quotientCLM_le (N : Submodule 𝕜 E) : ‖quotientCLM N‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- **Card `(7)`, attainment.**  Some unit annihilator functional realizes the quotient
distance. -/
theorem exists_conormal_eq_quotientDistance (N : Submodule 𝕜 E) (x : E) :
    ∃ f : StrongDual 𝕜 E, f ∈ conormal N ∧ ‖f‖ ≤ 1 ∧ ‖f x‖ = quotientDistance N x := by
  obtain ⟨g, hg1, hgx⟩ := exists_dual_vector'' 𝕜 (Submodule.Quotient.mk x : E ⧸ N)
  refine ⟨g.comp (quotientCLM N), ?_, ?_, ?_⟩
  · intro y hy
    have : (Submodule.Quotient.mk y : E ⧸ N) = 0 := (Submodule.Quotient.mk_eq_zero N).2 hy
    simp [this]
  · calc ‖g.comp (quotientCLM N)‖ ≤ ‖g‖ * ‖quotientCLM N‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by
          exact mul_le_mul hg1 (norm_quotientCLM_le N) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have : (g.comp (quotientCLM N)) x = ((‖(Submodule.Quotient.mk x : E ⧸ N)‖ : ℝ) : 𝕜) := by
      simpa using hgx
    rw [this, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), norm_quotient_mk]

/-- **Card `(7)`.**  The quotient distance is the greatest value attained on the conormal unit
ball. -/
theorem isGreatest_quotientDistance (N : Submodule 𝕜 E) (x : E) :
    IsGreatest {r : ℝ | ∃ f : StrongDual 𝕜 E, f ∈ conormal N ∧ ‖f‖ ≤ 1 ∧ ‖f x‖ = r}
      (quotientDistance N x) := by
  obtain ⟨f, hf, hf1, hfx⟩ := exists_conormal_eq_quotientDistance N x
  exact ⟨⟨f, hf, hf1, hfx⟩, by rintro r ⟨g, hg, hg1, rfl⟩; exact norm_le_quotientDistance hg hg1 x⟩

end Duality

/-! ## Modular covariance of the quotient distance -/

section Covariance

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Card `(5)`, `(8)`.**  An isometry carrying one filtration member onto another preserves the
quotient distance exactly. -/
theorem quotientDistance_isometry (N M : Submodule 𝕜 E) (T : E ≃ₗᵢ[𝕜] E)
    (hT : Submodule.map (T : E →ₗ[𝕜] E) N = M) (x : E) :
    quotientDistance M (T x) = quotientDistance N x := by
  have himg : (T : E → E) '' (N : Set E) = (M : Set E) := by
    rw [← hT]
    ext y
    simp
  rw [quotientDistance, quotientDistance, ← himg, Metric.infDist_image T.isometry]

end Covariance

/-! ## The half-sided modular filtration -/

section Filtration

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Card `(1)`, `(2)`, `(5)`.**  A nested filtration of a normed space together with an isometric
flow rescaling the filtration parameter by `e^{2πt}`. -/
structure ModularFiltration where
  /-- The filtration member at parameter `a`. -/
  layer : ℝ → Submodule 𝕜 E
  /-- The filtration is decreasing. -/
  antitone : ∀ ⦃a b : ℝ⦄, a ≤ b → layer b ≤ layer a
  /-- The modular flow. -/
  flow : ℝ → (E ≃ₗᵢ[𝕜] E)
  /-- The flow rescales the filtration parameter. -/
  covariant : ∀ t a : ℝ,
    Submodule.map ((flow t : E ≃ₗᵢ[𝕜] E) : E →ₗ[𝕜] E) (layer a)
      = layer (Real.exp (2 * Real.pi * t) * a)

variable {𝕜 E}

/-- **Card `(8)`.**  The quotient distance is exactly covariant for the modular flow. -/
theorem ModularFiltration.quotientDistance_flow (F : ModularFiltration 𝕜 E) (t a : ℝ) (x : E) :
    quotientDistance (F.layer (Real.exp (2 * Real.pi * t) * a)) (F.flow t x)
      = quotientDistance (F.layer a) x :=
  quotientDistance_isometry _ _ (F.flow t) (F.covariant t a) x

/-- **Card `(4)`, isometric form.**  The persistence row identifies the quotient of the larger
boundary defect by the intermediate layer with the smaller boundary defect. -/
noncomputable def persistenceQuotientIsometry {A B : Submodule 𝕜 E} (h : B ≤ A) :
    (E ⧸ B) ⧸ Submodule.map B.mkQ A ≃ₗᵢ[𝕜] E ⧸ A :=
  Submodule.quotientQuotientLIEQuotient (S := B) A h

end Filtration

/-! ## The bounded-dilation no-go -/

section BoundedNoGo

variable {A : Type*} [NormedRing A] [NormedSpace ℝ A]

/-- **Card `(9)`.**  A bounded element whose norm is preserved by a conjugation that rescales it by
a factor other than one is zero. -/
theorem eq_zero_of_isometric_scaling {P : A} {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≠ 1)
    (hnorm : ‖c • P‖ = ‖P‖) : P = 0 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc] at hnorm
  have hz : (c - 1) * ‖P‖ = 0 := by rw [sub_mul, one_mul, hnorm, sub_self]
  rcases mul_eq_zero.1 hz with h1 | h1
  · exact absurd (by linarith : c = 1) hc1
  · exact norm_eq_zero.1 h1

/-- **Card `(10)`.**  Any norm-preserving conjugate differs from the rescaled element by at least
the relative factor `|c − 1|`. -/
theorem scaling_defect_lower_bound {P Q : A} {c : ℝ} (hc : 0 ≤ c) (hnorm : ‖Q‖ = ‖P‖) :
    |c - 1| * ‖P‖ ≤ ‖Q - c • P‖ := by
  have h1 : |‖Q‖ - ‖c • P‖| ≤ ‖Q - c • P‖ := abs_norm_sub_norm_le _ _
  have h2 : ‖c • P‖ = c * ‖P‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  rw [hnorm, h2] at h1
  have h3 : |‖P‖ - c * ‖P‖| = |c - 1| * ‖P‖ := by
    rw [show ‖P‖ - c * ‖P‖ = (1 - c) * ‖P‖ by ring, abs_mul, abs_of_nonneg (norm_nonneg P),
      abs_sub_comm]
  rwa [h3] at h1

/-- **Card `(10)`, relative form.** -/
theorem scaling_relative_defect {P Q : A} {c : ℝ} (hc : 0 ≤ c) (hnorm : ‖Q‖ = ‖P‖)
    (hP : P ≠ 0) : |c - 1| ≤ ‖Q - c • P‖ / ‖P‖ := by
  have hpos : 0 < ‖P‖ := norm_pos_iff.2 hP
  rw [le_div_iff₀ hpos]
  exact scaling_defect_lower_bound hc hnorm

end BoundedNoGo

/-! ## Geometric moment growth excludes recurrence -/

section Moments

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The scaling law propagates to every power of the generator. -/
theorem pow_apply_of_scaling {P : Module.End ℂ H} {D : H ≃ₗ[ℂ] H} {c : ℂ}
    (hscale : ∀ x, P (D x) = c • D (P x)) (n : ℕ) (x : H) :
    (P ^ n) (D x) = c ^ n • D ((P ^ n) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hstep : (P ^ (n + 1)) (D x) = P ((P ^ n) (D x)) := by
      rw [pow_succ']
      rfl
    rw [hstep, ih x, map_smul, hscale, ← smul_assoc]
    have hp : (P ^ (n + 1)) x = P ((P ^ n) x) := by
      rw [pow_succ']
      rfl
    rw [hp, smul_eq_mul, ← pow_succ]

/-- **Card `(11)`.**  Every moment of the modular orbit grows by the geometric factor. -/
theorem inner_pow_scaling {P : Module.End ℂ H} {D : H ≃ₗ[ℂ] H} {c : ℂ}
    (hD : ∀ x y : H, ⟪D x, D y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hscale : ∀ x, P (D x) = c • D (P x)) (n : ℕ) (ψ : H) :
    ⟪D ψ, (P ^ n) (D ψ)⟫_ℂ = c ^ n * ⟪ψ, (P ^ n) ψ⟫_ℂ := by
  rw [pow_apply_of_scaling hscale n ψ, inner_smul_right, hD]

/-- **Card `(11)`, no recurrence.**  A strictly positive first moment grows without bound along the
modular orbit, so the orbit cannot return in the form topology. -/
theorem tendsto_moment_atTop {P : Module.End ℂ H} {D : H ≃ₗ[ℂ] H} {c : ℝ}
    (hD : ∀ x y : H, ⟪D x, D y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hscale : ∀ x, P (D x) = (c : ℂ) • D (P x)) (hc : 1 < c) {ψ : H}
    (hψ : 0 < (⟪ψ, P ψ⟫_ℂ).re) :
    Filter.Tendsto (fun n : ℕ => (⟪(D ^ n) ψ, P ((D ^ n) ψ)⟫_ℂ).re) Filter.atTop
      Filter.atTop := by
  have hiter : ∀ n : ℕ, (⟪(D ^ n) ψ, P ((D ^ n) ψ)⟫_ℂ).re = c ^ n * (⟪ψ, P ψ⟫_ℂ).re := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep : (D ^ (n + 1)) ψ = D ((D ^ n) ψ) := by
        rw [pow_succ']
        rfl
      have h1 := inner_pow_scaling (P := P) (D := D) (c := (c : ℂ)) hD hscale 1 ((D ^ n) ψ)
      simp only [pow_one] at h1
      rw [hstep, h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, ih]
      ring
  simp only [hiter]
  exact Filter.Tendsto.atTop_mul_const hψ (tendsto_pow_atTop_atTop_of_one_lt hc)

/-- **Card `(12)`.**  The characteristic function of the modular orbit is the characteristic
function of the rescaled generator. -/
theorem inner_characteristic_scaling {U : ℝ → Module.End ℂ H} {D : H ≃ₗ[ℂ] H} {c : ℝ}
    (hD : ∀ x y : H, ⟪D x, D y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hU : ∀ lam x, U lam (D x) = D (U (c * lam) x)) (lam : ℝ) (ψ : H) :
    ⟪D ψ, U lam (D ψ)⟫_ℂ = ⟪ψ, U (c * lam) ψ⟫_ℂ := by
  rw [hU, hD]

end Moments

/-! ## The extension phase splits -/

section Splitting

/-- **Card `(13)`.**  Every short exact sequence of vector spaces splits. -/
theorem exists_isCompl_vectorSpace {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (S : Submodule K V) : ∃ T, IsCompl S T :=
  Submodule.exists_isCompl S

/-- **Card `(13)`, Hilbert form.**  A complete subspace of an inner product space is complemented
by its orthogonal complement. -/
theorem isCompl_orthogonal_hilbert {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : Submodule ℂ H) [S.HasOrthogonalProjection] : IsCompl S Sᗮ :=
  Submodule.isCompl_orthogonal S

end Splitting

end HTGeometry.ConstraintRelativity
