import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Strong resolvent approximation of the identity

A densely defined operator `A` on a complex inner product space with a real lower bound
`floor` has the property that every sufficiently positive real shift `A + r` is bounded below
by `floor + r`.  If in addition each such shift is surjective — the standard criterion
distinguishing a self-adjoint operator from a merely symmetric one — then the normalized
resolvents `r (A + r)⁻¹` converge strongly to the identity as `r → ∞`.

The proof needs neither the spectral theorem nor a uniform boundedness principle.  On the
domain the exact algebraic identity

`(A + r) (r x_g - g) = -A g`,   where `(A + r) x_g = g`,

turns the lower bound directly into `‖r x_g - g‖ ≤ ‖A g‖ / (floor + r)`.  Density of the domain
and the resolvent bound `‖(A + r)⁻¹‖ ≤ (floor + r)⁻¹` then transfer this to every vector.

No resolvent operator is constructed: the statements quantify over arbitrary solutions of the
shifted equation, which the lower bound makes unique anyway.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A densely defined operator with a real lower bound all of whose admissible real shifts are
surjective.  This is the data carried by a lower-bounded self-adjoint operator; symmetry itself
is never used below. -/
structure LowerBoundedSource (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The dense operator domain. -/
  domain : Submodule ℂ H
  /-- The domain is dense. -/
  dense_domain : Dense (domain : Set H)
  /-- The operator itself. -/
  op : domain →ₗ[ℂ] H
  /-- A real lower bound for the quadratic form. -/
  floor : ℝ
  /-- The quadratic form is bounded below by `floor`. -/
  lower : ∀ x : domain, floor * ‖(x : H)‖ ^ (2 : ℕ) ≤ RCLike.re (inner ℂ (op x) (x : H))
  /-- Every shift above the lower bound is surjective. -/
  shift_surjective :
    ∀ r : ℝ, 0 < floor + r → ∀ f : H, ∃ x : domain, op x + (r : ℂ) • (x : H) = f

namespace LowerBoundedSource

variable (S : LowerBoundedSource H)

/-- The real shift `A + r` of the source, as a map on the domain. -/
def shift (r : ℝ) (x : S.domain) : H := S.op x + (r : ℂ) • (x : H)

@[simp] theorem shift_apply (r : ℝ) (x : S.domain) :
    S.shift r x = S.op x + (r : ℂ) • (x : H) := rfl

theorem shift_sub (r : ℝ) (x y : S.domain) :
    S.shift r (x - y) = S.shift r x - S.shift r y := by
  simp [shift, map_sub, smul_sub]
  abel

theorem shift_smul (r c : ℝ) (x : S.domain) :
    S.shift r ((c : ℂ) • x) = (c : ℂ) • S.shift r x := by
  simp [shift, smul_smul]
  ring_nf

/-- The real part of the shifted quadratic form. -/
theorem re_inner_shift (r : ℝ) (x : S.domain) :
    RCLike.re (inner ℂ (S.shift r x) (x : H))
      = RCLike.re (inner ℂ (S.op x) (x : H)) + r * ‖(x : H)‖ ^ (2 : ℕ) := by
  have hself : (inner ℂ (x : H) (x : H) : ℂ) = ((‖(x : H)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hs : inner ℂ ((r : ℂ) • (x : H)) (x : H) = ((r * ‖(x : H)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [inner_smul_left, hself, Complex.conj_ofReal]
    norm_cast
  have hre : RCLike.re (((r * ‖(x : H)‖ ^ (2 : ℕ) : ℝ) : ℂ)) = r * ‖(x : H)‖ ^ (2 : ℕ) := RCLike.ofReal_re _
  rw [shift, inner_add_left, hs, map_add, hre]

/-- **Lower bound for the shifted operator.** -/
theorem norm_shift_ge (r : ℝ) (x : S.domain) :
    (S.floor + r) * ‖(x : H)‖ ≤ ‖S.shift r x‖ := by
  rcases eq_or_lt_of_le (norm_nonneg (x : H)) with hx | hx
  · simp [← hx]
  · have key : (S.floor + r) * ‖(x : H)‖ ^ (2 : ℕ) ≤ ‖S.shift r x‖ * ‖(x : H)‖ := by
      calc (S.floor + r) * ‖(x : H)‖ ^ (2 : ℕ)
          = S.floor * ‖(x : H)‖ ^ (2 : ℕ) + r * ‖(x : H)‖ ^ (2 : ℕ) := by ring
        _ ≤ RCLike.re (inner ℂ (S.op x) (x : H)) + r * ‖(x : H)‖ ^ (2 : ℕ) := by
            have := S.lower x; linarith
        _ = RCLike.re (inner ℂ (S.shift r x) (x : H)) := (S.re_inner_shift r x).symm
        _ ≤ ‖S.shift r x‖ * ‖(x : H)‖ := re_inner_le_norm _ _
    have : (S.floor + r) * ‖(x : H)‖ * ‖(x : H)‖ ≤ ‖S.shift r x‖ * ‖(x : H)‖ := by
      calc (S.floor + r) * ‖(x : H)‖ * ‖(x : H)‖
          = (S.floor + r) * ‖(x : H)‖ ^ (2 : ℕ) := by ring
        _ ≤ _ := key
    exact le_of_mul_le_mul_right this hx

/-- **Resolvent bound.** -/
theorem norm_le_of_shift {r : ℝ} (hr : 0 < S.floor + r) (x : S.domain) :
    ‖(x : H)‖ ≤ ‖S.shift r x‖ / (S.floor + r) := by
  rw [le_div_iff₀ hr, mul_comm]
  exact S.norm_shift_ge r x

/-- The exact domain identity behind the resolvent approximation: if `(A + r) x = g` with
`g` in the domain, then `(A + r) (r x - g) = -A g`. -/
theorem shift_smul_sub (r : ℝ) {x g : S.domain} (hx : S.shift r x = (g : H)) :
    S.shift r ((r : ℂ) • x - g) = -S.op g := by
  rw [S.shift_sub, S.shift_smul r r x, hx]
  simp [shift]

/-- **Strong resolvent approximation of the identity.**  For every vector `f` and every
tolerance there is a shift threshold beyond which any solution `x` of `(A + r) x = f`
satisfies `‖r x - f‖ < ε`. -/
theorem exists_threshold_norm_smul_sub_lt (f : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ r : ℝ, R < r → ∀ x : S.domain, S.shift r x = f →
      ‖(r : ℂ) • (x : H) - f‖ < ε := by
  obtain ⟨g, hgmem, hg⟩ := S.dense_domain.exists_dist_lt f (by positivity : (0:ℝ) < ε / 6)
  set g' : S.domain := ⟨g, hgmem⟩ with hg'
  have hfg : ‖f - g‖ < ε / 6 := by rwa [← dist_eq_norm]
  refine ⟨max (max 1 (-(2 * S.floor))) (4 * ‖S.op g'‖ / ε), ?_⟩
  intro r hr x hx
  have hr1 : (1 : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) (lt_of_le_of_lt (le_max_left _ _) hr)
  have hrpos : 0 < r := lt_trans zero_lt_one hr1
  have hr2 : -(2 * S.floor) < r :=
    lt_of_le_of_lt (le_max_right _ _) (lt_of_le_of_lt (le_max_left _ _) hr)
  have hr3 : 4 * ‖S.op g'‖ / ε < r := lt_of_le_of_lt (le_max_right _ _) hr
  have hhalf : r / 2 < S.floor + r := by linarith
  have hpos : 0 < S.floor + r := lt_trans (by linarith) hhalf
  have hgap : 0 < ε * (S.floor + r - r / 2) := mul_pos hε (by linarith)
  -- the domain solution at the approximating vector
  obtain ⟨y, hy⟩ := S.shift_surjective r hpos g
  have hy' : S.shift r y = (g' : H) := hy
  -- distance between the two solutions
  have hdiff : S.shift r (x - y) = f - g := by rw [S.shift_sub, hx, hy']
  have h1 : ‖(x : H) - (y : H)‖ ≤ (ε / 6) / (S.floor + r) := by
    have hb := S.norm_le_of_shift hpos (x - y)
    rw [hdiff] at hb
    have hmono : ‖f - g‖ / (S.floor + r) ≤ (ε / 6) / (S.floor + r) := by
      have hinv : (0:ℝ) ≤ (S.floor + r)⁻¹ := le_of_lt (inv_pos.mpr hpos)
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hfg.le hinv
    calc ‖(x : H) - (y : H)‖ = ‖((x - y : S.domain) : H)‖ := by simp
      _ ≤ ‖f - g‖ / (S.floor + r) := hb
      _ ≤ (ε / 6) / (S.floor + r) := hmono
  have h1' : ‖(r : ℂ) • (x : H) - (r : ℂ) • (y : H)‖ ≤ ε / 3 := by
    have hnorm : ‖(r : ℂ) • (x : H) - (r : ℂ) • (y : H)‖ = r * ‖(x : H) - (y : H)‖ := by
      rw [← smul_sub, norm_smul]
      simp [abs_of_pos hrpos]
    rw [hnorm]
    have hb : r * ‖(x : H) - (y : H)‖ ≤ r * ((ε / 6) / (S.floor + r)) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hrpos)
    have hc : r * ((ε / 6) / (S.floor + r)) ≤ ε / 3 := by
      rw [mul_div_assoc', div_le_iff₀ hpos]
      nlinarith [hgap]
    linarith
  -- the approximation error at the domain vector
  have h2 : ‖(r : ℂ) • (y : H) - g‖ < ε / 2 := by
    have hid := S.shift_smul_sub r hy'
    have hb := S.norm_le_of_shift hpos ((r : ℂ) • y - g')
    rw [hid] at hb
    have hcast : ‖(((r : ℂ) • y - g' : S.domain) : H)‖ = ‖(r : ℂ) • (y : H) - g‖ := by
      simp [hg']
    rw [hcast] at hb
    have hb2 : ‖(r : ℂ) • (y : H) - g‖ ≤ ‖S.op g'‖ / (S.floor + r) := by
      simpa using hb
    have hlt : ‖S.op g'‖ / (S.floor + r) < ε / 2 := by
      rw [div_lt_iff₀ hpos]
      have hnum : 4 * ‖S.op g'‖ < r * ε := by
        rw [div_lt_iff₀ hε] at hr3; linarith
      nlinarith [hgap, hnum]
    linarith
  -- assemble
  have hsplit : (r : ℂ) • (x : H) - f
      = ((r : ℂ) • (x : H) - (r : ℂ) • (y : H)) + ((r : ℂ) • (y : H) - g) + (g - f) := by
    abel
  have hgf : ‖g - f‖ < ε / 6 := by rw [norm_sub_rev]; exact hfg
  calc ‖(r : ℂ) • (x : H) - f‖
      ≤ ‖((r : ℂ) • (x : H) - (r : ℂ) • (y : H)) + ((r : ℂ) • (y : H) - g)‖ + ‖g - f‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ ‖(r : ℂ) • (x : H) - (r : ℂ) • (y : H)‖ + ‖(r : ℂ) • (y : H) - g‖ + ‖g - f‖ := by
        have := norm_add_le ((r : ℂ) • (x : H) - (r : ℂ) • (y : H))
          ((r : ℂ) • (y : H) - g)
        linarith
    _ < ε := by linarith

/-- **Filter form of the strong resolvent limit.**  Any family of solutions of the shifted
equation, scaled by the shift, converges to the right-hand side. -/
theorem tendsto_smul_solution (f : H) (x : ℝ → S.domain)
    (hx : ∀ r : ℝ, S.shift r (x r) = f) :
    Filter.Tendsto (fun r : ℝ => (r : ℂ) • ((x r : H))) atTop (𝓝 f) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hR⟩ := S.exists_threshold_norm_smul_sub_lt f hε
  refine ⟨R + 1, fun r hr => ?_⟩
  rw [dist_eq_norm]
  exact hR r (by linarith) (x r) (hx r)

end LowerBoundedSource

/-! ## The free source

The zero operator on the whole space is a lower-bounded source with floor `0`.  It certifies
that the structure is inhabited and that the strong resolvent limit above is not vacuous. -/

/-- The zero operator, viewed as a lower-bounded source with floor `0`. -/
def freeSource (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    LowerBoundedSource H where
  domain := ⊤
  dense_domain := by
    have : ((⊤ : Submodule ℂ H) : Set H) = Set.univ := by ext; simp
    rw [this]; exact dense_univ
  op := 0
  floor := 0
  lower := by intro x; simp
  shift_surjective := by
    intro r hr f
    refine ⟨⟨(r : ℂ)⁻¹ • f, Submodule.mem_top⟩, ?_⟩
    have hr0 : (r : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      simp at hr
      linarith
    simp [smul_smul, mul_inv_cancel₀ hr0]

@[simp] theorem freeSource_floor (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    (freeSource H).floor = 0 := rfl

end GaloisForLFunctions.HTGeometry
