import GaloisForLFunctions.HTGeometry.UnitriangularRepairGenealogyFinite
import GaloisForLFunctions.HTGeometry.ConstitutiveToeplitzDefectIndex
import GaloisForLFunctions.HTGeometry.WeightedOrbitInductionGap
import GaloisForLFunctions.HTGeometry.ObserverHorizonStability
import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators

/-!
# Cofinal unitriangular repair genealogy: phase trichotomy, admission, compact repair, index

On `ℓ²(ℕ)` with forward shift `S` and backward shift `B = S*`, the stationary sequential repair
certificate `e_n ∼ α e_{n-1}` completes to the genealogy operator `G_α = 1 - α B` (GR.9).

* **Subcritical chamber** `0 ≤ α < 1`: `G_α` is a bounded isomorphism with Neumann inverse
  `∑ α^k B^k` of norm at most `(1 - α)⁻¹` (GR.10).
* **Critical chamber** `α = 1`: `G_1` is injective with dense, proper, nonclosed range; the unit
  histories `u_N = (N+1)^{-1/2} ∑_{n ≤ N} e_n` satisfy `‖G_1 u_N‖ = (N+1)^{-1/2}` (GR.11)–(GR.12).
* **Supercritical chamber** `α > 1`: `G_α` is surjective with kernel `ℂ g_α`,
  `g_α = (α^{-n})_n` (GR.13), bounded right inverse `R_α = -α⁻¹ (1 - α⁻¹ S)⁻¹ S` with
  `‖R_α‖ ≤ (α - 1)⁻¹` (GR.14), and `‖g_α‖² = α²/(α² - 1)` (GR.15).
* **Admission** (GR.17)–(GR.18): the algebraic semantic reader `b_α(x) = ∑ α^n x_n` satisfies
  `b_α G_α z = z_0` on finitely supported sequences in every chamber, and extends continuously to
  `ℓ²` exactly when `α < 1`.
* **Compact repair** (GR.19)–(GR.22): the joint observer `x ↦ (A x, G_α x)` is bounded below for
  every `A` when `α < 1`, for no compact `A` when `α = 1`, and exactly when `A g_α ≠ 0` when
  `α > 1`, with the explicit joint reconstruction `x = J_α(G_α x) + (⟨g_α, x⟩/‖g_α‖²) g_α`.
* **Reciprocity and index** (GR.23)–(GR.25): `G_α = -α B G_{1/α}^*`, the terminal projections
  tend strongly to zero with norm one, and the Fredholm index is `0`, undefined, `1` in the three
  chambers.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology ContinuousLinearMap
open scoped InnerProductSpace ENNReal

/-! ## Shift calculus -/

theorem backOp_one_pow (k : ℕ) : backOp 1 ^ k = backOp k := by
  induction k with
  | zero => ext f n; simp
  | succ k ih =>
      rw [pow_succ, ih]
      ext f n
      simp [mul_apply_eq_comp, add_assoc]

theorem shiftOp_one_apply_zero (f : ToeplitzSpace) : (shiftOp 1 f : ℕ → ℂ) 0 = 0 := by
  simp [shiftFun]

theorem shiftOp_one_apply_succ (f : ToeplitzSpace) (n : ℕ) :
    (shiftOp 1 f : ℕ → ℂ) (n + 1) = (f : ℕ → ℂ) n := by
  rw [shiftOp_apply]; exact shiftFun_add 1 _ n

theorem norm_backOp_le (n : ℕ) : ‖backOp n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [one_mul]; exact norm_backLinear_le n f

theorem norm_shiftOp_le (n : ℕ) : ‖shiftOp n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [one_mul]; exact le_of_eq ((shiftIsom n).norm_map f)

theorem adjoint_backOp (n : ℕ) : adjoint (backOp n) = shiftOp n := by
  rw [← adjoint_shiftOp, adjoint_adjoint]

/-- An `ℓ²(ℕ)` sequence tends to zero. -/
theorem tendsto_toeplitz_coord (x : ToeplitzSpace) :
    Tendsto (fun n => (x : ℕ → ℂ) n) atTop (𝓝 0) := by
  have hs : Summable fun n => ‖(x : ℕ → ℂ) n‖ ^ 2 := by
    have := (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa using this
  have h := hs.tendsto_atTop_zero
  have h2 : Tendsto (fun n => ‖(x : ℕ → ℂ) n‖) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h
    simp only [Function.comp_def, Real.sqrt_zero] at this
    refine this.congr fun n => ?_
    rw [Real.sqrt_sq (norm_nonneg _)]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr h2

/-! ## The genealogy operator -/

/-- The cofinal genealogy formation operator `G_α = 1 - α B` (GR.9). -/
def cofinalGenealogy (α : ℝ) : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  ContinuousLinearMap.id ℂ ToeplitzSpace - (α : ℂ) • backOp 1

@[simp] theorem cofinalGenealogy_apply (α : ℝ) (x : ToeplitzSpace) (n : ℕ) :
    (cofinalGenealogy α x : ℕ → ℂ) n = (x : ℕ → ℂ) n - α * (x : ℕ → ℂ) (n + 1) := by
  show ((x - ((α : ℂ) • backOp 1) x : ToeplitzSpace) : ℕ → ℂ) n = _
  rw [lp.coeFn_sub, Pi.sub_apply, FunLike.coe_smul, Pi.smul_apply, lp.coeFn_smul,
    Pi.smul_apply, backOp_apply, smul_eq_mul]

theorem adjoint_cofinalGenealogy (α : ℝ) :
    adjoint (cofinalGenealogy α) = ContinuousLinearMap.id ℂ ToeplitzSpace - (α : ℂ) • shiftOp 1 := by
  rw [cofinalGenealogy, map_sub, adjoint_id, map_smulₛₗ, adjoint_backOp]
  simp

/-! ## Subcritical chamber -/

theorem norm_smul_backOp_lt {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    ‖(α : ℂ) • backOp 1‖ < 1 := by
  calc ‖(α : ℂ) • backOp 1‖ ≤ ‖(α : ℂ)‖ * ‖backOp 1‖ := ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ α * 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
        exact mul_le_mul_of_nonneg_left (norm_backOp_le 1) h0
    _ < 1 := by linarith

/-- In the subcritical chamber `G_α` is a unit of the operator algebra. -/
def cofinalGenealogyUnit {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    (ToeplitzSpace →L[ℂ] ToeplitzSpace)ˣ :=
  Units.oneSub ((α : ℂ) • backOp 1) (norm_smul_backOp_lt h0 h1)

theorem coe_cofinalGenealogyUnit {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    (cofinalGenealogyUnit h0 h1 : ToeplitzSpace →L[ℂ] ToeplitzSpace) = cofinalGenealogy α := rfl

/-- **(GR.10)** The inverse is the Neumann series `∑ α^k B^k`. -/
theorem cofinalGenealogyUnit_inv_eq_tsum {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    ((cofinalGenealogyUnit h0 h1)⁻¹ : (ToeplitzSpace →L[ℂ] ToeplitzSpace)ˣ).val =
      ∑' k : ℕ, ((α : ℂ) ^ k) • backOp k := by
  change ∑' k : ℕ, ((α : ℂ) • backOp 1) ^ k = _
  congr 1
  funext k
  rw [smul_pow, backOp_one_pow]

/-- **(GR.10)** `‖G_α⁻¹‖ ≤ (1 - α)⁻¹`. -/
theorem norm_cofinalGenealogyUnit_inv_le {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    ‖((cofinalGenealogyUnit h0 h1)⁻¹ : (ToeplitzSpace →L[ℂ] ToeplitzSpace)ˣ).val‖ ≤
      (1 - α)⁻¹ := by
  have hlt := norm_smul_backOp_lt h0 h1
  have hbound := tsum_geometric_le_of_norm_lt_one _ hlt
  have hle : ‖(α : ℂ) • backOp 1‖ ≤ α := by
    calc ‖(α : ℂ) • backOp 1‖ ≤ ‖(α : ℂ)‖ * ‖backOp 1‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ α * 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
          exact mul_le_mul_of_nonneg_left (norm_backOp_le 1) h0
      _ = α := mul_one α
  have hone : ‖(1 : ToeplitzSpace →L[ℂ] ToeplitzSpace)‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  change ‖∑' k : ℕ, ((α : ℂ) • backOp 1) ^ k‖ ≤ _
  calc ‖∑' k : ℕ, ((α : ℂ) • backOp 1) ^ k‖
      ≤ ‖(1 : ToeplitzSpace →L[ℂ] ToeplitzSpace)‖ - 1 + (1 - ‖(α : ℂ) • backOp 1‖)⁻¹ := hbound
    _ ≤ (1 - ‖(α : ℂ) • backOp 1‖)⁻¹ := by linarith
    _ ≤ (1 - α)⁻¹ := by
        apply inv_anti₀ (by linarith)
        linarith

theorem cofinalGenealogy_isUnit {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    IsUnit (cofinalGenealogy α) := ⟨cofinalGenealogyUnit h0 h1, rfl⟩

/-- In the subcritical chamber the genealogy is bounded below. -/
theorem cofinalGenealogy_boundedBelow {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (x : ToeplitzSpace) :
    (1 - α) * ‖x‖ ≤ ‖cofinalGenealogy α x‖ := by
  set u := cofinalGenealogyUnit h0 h1
  have hx : x = (u⁻¹ : (ToeplitzSpace →L[ℂ] ToeplitzSpace)ˣ).val (cofinalGenealogy α x) := by
    have h := congrArg (fun T : ToeplitzSpace →L[ℂ] ToeplitzSpace => T x) u.inv_mul
    exact h.symm
  have hle : ‖x‖ ≤ (1 - α)⁻¹ * ‖cofinalGenealogy α x‖ := by
    conv_lhs => rw [hx]
    exact ((u⁻¹ : (ToeplitzSpace →L[ℂ] ToeplitzSpace)ˣ).val.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_cofinalGenealogyUnit_inv_le h0 h1) (norm_nonneg _))
  have hpos : 0 < 1 - α := by linarith
  rw [inv_mul_eq_div, le_div_iff₀ hpos] at hle
  linarith

/-! ## Critical chamber -/

/-- Initial coordinate block `∑_{n ≤ N} e_n`. -/
def initialBlock (N : ℕ) : ToeplitzSpace :=
  ∑ n ∈ Finset.range (N + 1), lp.single 2 n (1 : ℂ)

theorem initialBlock_apply (N k : ℕ) :
    (initialBlock N : ℕ → ℂ) k = if k ≤ N then 1 else 0 := by
  rw [initialBlock, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply, Pi.single_apply]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem inner_single_initialBlock (N k : ℕ) :
    ⟪(lp.single 2 k (1 : ℂ) : ToeplitzSpace), initialBlock N⟫_ℂ = if k ≤ N then 1 else 0 := by
  rw [lp.inner_single_left, initialBlock_apply]
  split_ifs <;> simp

theorem norm_sq_initialBlock (N : ℕ) : ‖initialBlock N‖ ^ 2 = (N + 1 : ℝ) := by
  have h : ⟪initialBlock N, initialBlock N⟫_ℂ = ((N + 1 : ℕ) : ℂ) := by
    rw [show ⟪initialBlock N, initialBlock N⟫_ℂ = ∑ k ∈ Finset.range (N + 1),
        ⟪(lp.single 2 k (1 : ℂ) : ToeplitzSpace), initialBlock N⟫_ℂ by
      rw [initialBlock, sum_inner]]
    have : ∀ k ∈ Finset.range (N + 1),
        ⟪(lp.single 2 k (1 : ℂ) : ToeplitzSpace), initialBlock N⟫_ℂ = 1 := by
      intro k hk
      rw [inner_single_initialBlock, if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [inner_self_eq_norm_sq_to_K] at h
  have h' : ((‖initialBlock N‖ ^ 2 : ℝ) : ℂ) = ((N + 1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow]; push_cast at h ⊢; exact h
  exact Complex.ofReal_injective h'

/-- The critical genealogy of an initial block is its terminal basis vector. -/
theorem cofinalGenealogy_one_initialBlock (N : ℕ) :
    cofinalGenealogy 1 (initialBlock N) = lp.single 2 N (1 : ℂ) := by
  ext k
  rw [cofinalGenealogy_apply, initialBlock_apply, initialBlock_apply, lp.single_apply,
    Pi.single_apply]
  rcases lt_trichotomy k N with h | h | h
  · rw [if_pos h.le, if_pos (by omega : k + 1 ≤ N), if_neg h.ne]; simp
  · subst h; rw [if_pos le_rfl, if_neg (by omega), if_pos rfl]; simp
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp

/-- The critical unit histories `u_N = (N+1)^{-1/2} ∑_{n ≤ N} e_n` (GR.11). -/
def criticalHistory (N : ℕ) : ToeplitzSpace :=
  ((Real.sqrt (N + 1 : ℝ))⁻¹ : ℂ) • initialBlock N

theorem norm_criticalHistory (N : ℕ) : ‖criticalHistory N‖ = 1 := by
  have hpos : 0 < Real.sqrt (N + 1 : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hnorm : ‖initialBlock N‖ = Real.sqrt (N + 1 : ℝ) := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_initialBlock]
  rw [criticalHistory, norm_smul, hnorm, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']

/-- **(GR.12)** `‖G_1 u_N‖ = (N+1)^{-1/2}`. -/
theorem norm_cofinalGenealogy_one_criticalHistory (N : ℕ) :
    ‖cofinalGenealogy 1 (criticalHistory N)‖ = (Real.sqrt (N + 1 : ℝ))⁻¹ := by
  have hpos : 0 < Real.sqrt (N + 1 : ℝ) := Real.sqrt_pos.2 (by positivity)
  rw [criticalHistory, map_smul, cofinalGenealogy_one_initialBlock]
  rw [norm_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one, mul_one, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]

theorem tendsto_norm_cofinalGenealogy_one_criticalHistory :
    Tendsto (fun N : ℕ => ‖cofinalGenealogy 1 (criticalHistory N)‖) atTop (𝓝 0) := by
  simp_rw [norm_cofinalGenealogy_one_criticalHistory]
  have h : Tendsto (fun N : ℕ => Real.sqrt (N + 1 : ℝ)) atTop atTop := by
    refine Real.tendsto_sqrt_atTop.comp ?_
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  exact h.inv_tendsto_atTop

/-- The critical genealogy is not bounded below. -/
theorem cofinalGenealogy_one_not_boundedBelow :
    ¬ ∃ c > 0, ∀ x, c * ‖x‖ ≤ ‖cofinalGenealogy 1 x‖ := by
  rintro ⟨c, hc, h⟩
  have hev := tendsto_norm_cofinalGenealogy_one_criticalHistory.eventually
    (gt_mem_nhds hc)
  obtain ⟨N, hN⟩ := hev.exists
  have := h (criticalHistory N)
  rw [norm_criticalHistory, mul_one] at this
  linarith

/-- **Critical chamber: injectivity** (`ker G_1 = 0`: no hidden lineage is born). -/
theorem cofinalGenealogy_one_injective : Function.Injective (cofinalGenealogy 1) := by
  intro x y hxy
  rw [← sub_eq_zero]
  set x := x - y with hxdef
  have hx : cofinalGenealogy 1 x = 0 := by rw [hxdef, map_sub, hxy, sub_self]
  clear_value x
  have hcoord : ∀ n, (x : ℕ → ℂ) n = (x : ℕ → ℂ) 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        have := congrArg (fun y : ToeplitzSpace => (y : ℕ → ℂ) n) hx
        simp only [cofinalGenealogy_apply, Complex.ofReal_one, one_mul, lp.coeFn_zero,
          Pi.zero_apply] at this
        rw [← ih]
        exact (sub_eq_zero.mp this).symm
  have hlim := tendsto_toeplitz_coord x
  simp_rw [hcoord] at hlim
  have h0 : (x : ℕ → ℂ) 0 = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  ext n
  rw [hcoord n, h0]
  rfl

/-- The adjoint `1 - S` of the critical genealogy is injective. -/
theorem adjoint_cofinalGenealogy_one_injective :
    LinearMap.ker (adjoint (cofinalGenealogy 1) : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro y hy
  have hcoord : ∀ n, (y : ℕ → ℂ) n = 0 := by
    intro n
    induction n with
    | zero =>
        have := congrArg (fun z : ToeplitzSpace => (z : ℕ → ℂ) 0) hy
        have hform : ((adjoint (cofinalGenealogy 1) y : ToeplitzSpace) : ℕ → ℂ) 0 =
            (y : ℕ → ℂ) 0 := by
          rw [adjoint_cofinalGenealogy]
          show ((y - (((1 : ℝ) : ℂ) • shiftOp 1) y : ToeplitzSpace) : ℕ → ℂ) 0 = _
          rw [lp.coeFn_sub, Pi.sub_apply, FunLike.coe_smul, Pi.smul_apply, Complex.ofReal_one,
            one_smul, shiftOp_one_apply_zero, sub_zero]
        simpa only [ContinuousLinearMap.coe_coe, hform, lp.coeFn_zero, Pi.zero_apply] using this
    | succ n ih =>
        have := congrArg (fun z : ToeplitzSpace => (z : ℕ → ℂ) (n + 1)) hy
        have hform : ((adjoint (cofinalGenealogy 1) y : ToeplitzSpace) : ℕ → ℂ) (n + 1) =
            (y : ℕ → ℂ) (n + 1) - (y : ℕ → ℂ) n := by
          rw [adjoint_cofinalGenealogy]
          show ((y - (((1 : ℝ) : ℂ) • shiftOp 1) y : ToeplitzSpace) : ℕ → ℂ) (n + 1) = _
          rw [lp.coeFn_sub, Pi.sub_apply, FunLike.coe_smul, Pi.smul_apply, Complex.ofReal_one,
            one_smul, shiftOp_one_apply_succ]
        simp only [ContinuousLinearMap.coe_coe, hform, ih, sub_zero, lp.coeFn_zero,
          Pi.zero_apply] at this
        exact this
  ext n
  rw [hcoord n]
  rfl

/-- **Critical chamber: dense range.** -/
theorem dense_range_cofinalGenealogy_one : Dense (Set.range (cofinalGenealogy 1)) := by
  have hperp : (LinearMap.range (cofinalGenealogy 1 : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace))ᗮ = ⊥ := by
    rw [ContinuousLinearMap.orthogonal_range]
    exact adjoint_cofinalGenealogy_one_injective
  have hclos : (LinearMap.range
      (cofinalGenealogy 1 : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace)).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hperp, Submodule.bot_orthogonal_eq_top]
  have h := Submodule.dense_iff_topologicalClosure_eq_top.mpr hclos
  simpa [LinearMap.coe_range] using h

/-- **Critical chamber: the range is not closed.** -/
theorem not_isClosed_range_cofinalGenealogy_one : ¬ IsClosed (Set.range (cofinalGenealogy 1)) := by
  intro hcl
  apply cofinalGenealogy_one_not_boundedBelow
  rw [exists_pos_mul_norm_le_iff]
  exact ⟨LinearMap.ker_eq_bot.mpr cofinalGenealogy_one_injective, hcl⟩

/-- **Critical chamber: the range is proper.** -/
theorem range_cofinalGenealogy_one_ne_univ : Set.range (cofinalGenealogy 1) ≠ Set.univ := by
  intro h
  apply not_isClosed_range_cofinalGenealogy_one
  rw [h]
  exact isClosed_univ

/-! ## Supercritical chamber -/

theorem norm_inv_smul_shiftOp_lt {α : ℝ} (hα : 1 < α) :
    ‖((α⁻¹ : ℝ) : ℂ) • shiftOp 1‖ < 1 := by
  have hα0 : 0 < α := by linarith
  calc ‖((α⁻¹ : ℝ) : ℂ) • shiftOp 1‖ ≤ ‖((α⁻¹ : ℝ) : ℂ)‖ * ‖shiftOp 1‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ α⁻¹ * 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hα0)]
        exact mul_le_mul_of_nonneg_left (norm_shiftOp_le 1) (inv_pos.mpr hα0).le
    _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ hα

/-- The invertible forward factor `1 - α⁻¹ S` of the supercritical genealogy. -/
def supercriticalShiftUnit {α : ℝ} (hα : 1 < α) : (ToeplitzSpace →L[ℂ] ToeplitzSpace)ˣ :=
  Units.oneSub (((α⁻¹ : ℝ) : ℂ) • shiftOp 1) (norm_inv_smul_shiftOp_lt hα)

theorem coe_supercriticalShiftUnit {α : ℝ} (hα : 1 < α) :
    (supercriticalShiftUnit hα : ToeplitzSpace →L[ℂ] ToeplitzSpace) =
      ContinuousLinearMap.id ℂ ToeplitzSpace - ((α⁻¹ : ℝ) : ℂ) • shiftOp 1 := rfl

theorem norm_supercriticalShiftUnit_inv_le {α : ℝ} (hα : 1 < α) :
    ‖((supercriticalShiftUnit hα)⁻¹ : (ToeplitzSpace →L[ℂ] ToeplitzSpace)ˣ).val‖ ≤
      (1 - α⁻¹)⁻¹ := by
  have hα0 : 0 < α := by linarith
  have hlt := norm_inv_smul_shiftOp_lt hα
  have hbound := tsum_geometric_le_of_norm_lt_one _ hlt
  have hle : ‖((α⁻¹ : ℝ) : ℂ) • shiftOp 1‖ ≤ α⁻¹ := by
    calc ‖((α⁻¹ : ℝ) : ℂ) • shiftOp 1‖ ≤ ‖((α⁻¹ : ℝ) : ℂ)‖ * ‖shiftOp 1‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ α⁻¹ * 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hα0)]
          exact mul_le_mul_of_nonneg_left (norm_shiftOp_le 1) (inv_pos.mpr hα0).le
      _ = α⁻¹ := mul_one _
  have hone : ‖(1 : ToeplitzSpace →L[ℂ] ToeplitzSpace)‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  have hinvlt : α⁻¹ < 1 := inv_lt_one_of_one_lt₀ hα
  change ‖∑' k : ℕ, (((α⁻¹ : ℝ) : ℂ) • shiftOp 1) ^ k‖ ≤ _
  calc ‖∑' k : ℕ, (((α⁻¹ : ℝ) : ℂ) • shiftOp 1) ^ k‖
      ≤ ‖(1 : ToeplitzSpace →L[ℂ] ToeplitzSpace)‖ - 1 +
          (1 - ‖((α⁻¹ : ℝ) : ℂ) • shiftOp 1‖)⁻¹ := hbound
    _ ≤ (1 - ‖((α⁻¹ : ℝ) : ℂ) • shiftOp 1‖)⁻¹ := by linarith
    _ ≤ (1 - α⁻¹)⁻¹ := by
        apply inv_anti₀ (by linarith)
        linarith

/-- **(GR.16)** `G_α = -α B (1 - α⁻¹ S)`. -/
theorem cofinalGenealogy_eq_neg_smul_backOp_comp {α : ℝ} (hα : α ≠ 0) :
    cofinalGenealogy α = (-(α : ℂ)) • (backOp 1 ∘L
      (ContinuousLinearMap.id ℂ ToeplitzSpace - ((α⁻¹ : ℝ) : ℂ) • shiftOp 1)) := by
  ext x n
  rw [cofinalGenealogy_apply]
  have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast hα
  show _ = (((-(α : ℂ)) • (backOp 1 (x - (((α⁻¹ : ℝ) : ℂ) • shiftOp 1) x)) : ToeplitzSpace) :
    ℕ → ℂ) n
  rw [lp.coeFn_smul, Pi.smul_apply, backOp_apply, lp.coeFn_sub, Pi.sub_apply, FunLike.coe_smul,
    Pi.smul_apply, lp.coeFn_smul, Pi.smul_apply, shiftOp_one_apply_succ, smul_eq_mul, smul_eq_mul]
  push_cast
  field_simp
  ring

/-- **(GR.14)** The bounded right inverse `R_α = -α⁻¹ (1 - α⁻¹ S)⁻¹ S`. -/
def supercriticalRightInverse {α : ℝ} (hα : 1 < α) : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  (-((α⁻¹ : ℝ) : ℂ)) •
    (((supercriticalShiftUnit hα)⁻¹ : (ToeplitzSpace →L[ℂ] ToeplitzSpace)ˣ).val ∘L shiftOp 1)

theorem cofinalGenealogy_comp_supercriticalRightInverse {α : ℝ} (hα : 1 < α) :
    cofinalGenealogy α ∘L supercriticalRightInverse hα = ContinuousLinearMap.id ℂ ToeplitzSpace := by
  have hα0 : α ≠ 0 := by positivity
  rw [cofinalGenealogy_eq_neg_smul_backOp_comp hα0, supercriticalRightInverse,
    ← coe_supercriticalShiftUnit hα]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
  have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast hα0
  have hscal : -(α : ℂ) * -((α⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp
  rw [hscal, one_smul]
  have hunit : (supercriticalShiftUnit hα : ToeplitzSpace →L[ℂ] ToeplitzSpace) ∘L
      ((supercriticalShiftUnit hα)⁻¹ : (ToeplitzSpace →L[ℂ] ToeplitzSpace)ˣ).val =
      ContinuousLinearMap.id ℂ ToeplitzSpace := (supercriticalShiftUnit hα).mul_inv
  rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc _ _ (shiftOp 1), hunit,
    ContinuousLinearMap.id_comp, backOp_comp_shiftOp]

/-- **(GR.14)** `‖R_α‖ ≤ (α - 1)⁻¹`. -/
theorem norm_supercriticalRightInverse_le {α : ℝ} (hα : 1 < α) :
    ‖supercriticalRightInverse hα‖ ≤ (α - 1)⁻¹ := by
  have hα0 : 0 < α := by linarith
  have hinvlt : α⁻¹ < 1 := inv_lt_one_of_one_lt₀ hα
  calc ‖supercriticalRightInverse hα‖
      ≤ ‖-((α⁻¹ : ℝ) : ℂ)‖ *
          (‖((supercriticalShiftUnit hα)⁻¹ : (ToeplitzSpace →L[ℂ] ToeplitzSpace)ˣ).val‖ *
            ‖shiftOp 1‖) :=
        (ContinuousLinearMap.opNorm_smul_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ α⁻¹ * ((1 - α⁻¹)⁻¹ * 1) := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hα0)]
        gcongr
        · exact norm_supercriticalShiftUnit_inv_le hα
        · exact norm_shiftOp_le 1
    _ = (α - 1)⁻¹ := by
        field_simp

theorem cofinalGenealogy_surjective {α : ℝ} (hα : 1 < α) :
    Function.Surjective (cofinalGenealogy α) := fun y =>
  ⟨supercriticalRightInverse hα y, by
    have h := congrArg (fun T : ToeplitzSpace →L[ℂ] ToeplitzSpace => T y)
      (cofinalGenealogy_comp_supercriticalRightInverse hα)
    exact h⟩

theorem summable_hiddenLineage_sq {α : ℝ} (hα : 1 < α) :
    Summable fun n : ℕ => ‖(((α⁻¹ ^ n : ℝ)) : ℂ)‖ ^ 2 := by
  have hα0 : 0 < α := by linarith
  have hr : α⁻¹ ^ 2 < 1 := pow_lt_one₀ (inv_pos.mpr hα0).le (inv_lt_one_of_one_lt₀ hα) two_ne_zero
  refine (summable_geometric_of_lt_one (by positivity) hr).congr fun n => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  ring

/-- **(GR.13)** The born hidden lineage `g_α = (1, α⁻¹, α⁻², …)`. -/
def hiddenLineage {α : ℝ} (hα : 1 < α) : ToeplitzSpace :=
  ⟨fun n => ((α⁻¹ ^ n : ℝ) : ℂ), memℓp_gen (by
    simpa using summable_hiddenLineage_sq hα)⟩

@[simp] theorem hiddenLineage_apply {α : ℝ} (hα : 1 < α) (n : ℕ) :
    (hiddenLineage hα : ℕ → ℂ) n = ((α⁻¹ ^ n : ℝ) : ℂ) := rfl

theorem cofinalGenealogy_hiddenLineage {α : ℝ} (hα : 1 < α) :
    cofinalGenealogy α (hiddenLineage hα) = 0 := by
  have hα0 : α ≠ 0 := by positivity
  have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast hα0
  ext n
  rw [cofinalGenealogy_apply, hiddenLineage_apply, hiddenLineage_apply]
  simp only [lp.coeFn_zero, Pi.zero_apply]
  push_cast
  rw [pow_succ]
  field_simp
  ring

theorem hiddenLineage_ne_zero {α : ℝ} (hα : 1 < α) : hiddenLineage hα ≠ 0 := by
  intro h
  have := congrArg (fun x : ToeplitzSpace => (x : ℕ → ℂ) 0) h
  simp at this

/-- **(GR.15)** `‖g_α‖² = α² / (α² - 1)`. -/
theorem norm_sq_hiddenLineage {α : ℝ} (hα : 1 < α) :
    ‖hiddenLineage hα‖ ^ 2 = α ^ 2 / (α ^ 2 - 1) := by
  have hα0 : 0 < α := by linarith
  have hr : α⁻¹ ^ 2 < 1 := pow_lt_one₀ (inv_pos.mpr hα0).le (inv_lt_one_of_one_lt₀ hα) two_ne_zero
  have hinner : ⟪hiddenLineage hα, hiddenLineage hα⟫_ℂ = ((α ^ 2 / (α ^ 2 - 1) : ℝ) : ℂ) := by
    rw [lp.inner_eq_tsum]
    have hterm : ∀ n : ℕ, ⟪(hiddenLineage hα : ℕ → ℂ) n, (hiddenLineage hα : ℕ → ℂ) n⟫_ℂ =
        (((α⁻¹ ^ 2) ^ n : ℝ) : ℂ) := by
      intro n
      rw [hiddenLineage_apply, RCLike.inner_apply, Complex.conj_ofReal]
      push_cast
      ring
    simp_rw [hterm]
    rw [← Complex.ofReal_tsum, tsum_geometric_of_lt_one (by positivity) hr]
    congr 1
    have hα2 : α ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have h' : ((‖hiddenLineage hα‖ ^ 2 : ℝ) : ℂ) = ((α ^ 2 / (α ^ 2 - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow]; exact hinner
  exact Complex.ofReal_injective h'

/-- The hidden-lineage mass diverges as the critical wall is approached from above. -/
theorem tendsto_hiddenLineage_mass :
    Tendsto (fun α : ℝ => α ^ 2 / (α ^ 2 - 1)) (𝓝[>] 1) atTop := by
  have hnum : Tendsto (fun α : ℝ => α ^ 2) (𝓝[>] 1) (𝓝 1) := by
    have := ((continuous_pow 2).tendsto (1 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    simpa using this
  have hden : Tendsto (fun α : ℝ => α ^ 2 - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun α : ℝ => α ^ 2 - 1 := by fun_prop
      have := (hc.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with α hα
      simp only [Set.mem_Ioi] at hα ⊢
      nlinarith
  exact hnum.pos_mul_atTop one_pos (tendsto_inv_nhdsGT_zero.comp hden) |>.congr fun α => by
    simp [div_eq_mul_inv]

/-- **(GR.13)** `ker G_α = ℂ g_α`. -/
theorem ker_cofinalGenealogy {α : ℝ} (hα : 1 < α) :
    LinearMap.ker (cofinalGenealogy α : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace) =
      ℂ ∙ hiddenLineage hα := by
  have hα0 : α ≠ 0 := by positivity
  apply le_antisymm
  · intro x hx
    have hx' : cofinalGenealogy α x = 0 := hx
    have hstep : ∀ n, (x : ℕ → ℂ) (n + 1) = (α⁻¹ : ℂ) * (x : ℕ → ℂ) n := by
      intro n
      have := congrArg (fun y : ToeplitzSpace => (y : ℕ → ℂ) n) hx'
      simp only [cofinalGenealogy_apply, lp.coeFn_zero, Pi.zero_apply] at this
      have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast hα0
      field_simp
      linear_combination -this
    have hcoord : ∀ n, (x : ℕ → ℂ) n = (x : ℕ → ℂ) 0 * ((α⁻¹ ^ n : ℝ) : ℂ) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [hstep, ih]; push_cast; ring
    rw [Submodule.mem_span_singleton]
    refine ⟨(x : ℕ → ℂ) 0, ?_⟩
    ext n
    rw [lp.coeFn_smul, Pi.smul_apply, hiddenLineage_apply, hcoord n, smul_eq_mul]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact cofinalGenealogy_hiddenLineage hα

/-! ## Admission: the algebraic semantic reader -/

/-- A finitely supported history as an `ℓ²` vector. -/
def finiteHistory (l : ℕ →₀ ℂ) : ToeplitzSpace :=
  l.sum fun n c => lp.single 2 n c

theorem finiteHistory_apply (l : ℕ →₀ ℂ) (k : ℕ) : (finiteHistory l : ℕ → ℂ) k = l k := by
  rw [finiteHistory, Finsupp.sum, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply, Pi.single_apply]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

/-- **(GR.17)** The algebraic semantic reader `b_α(x) = ∑ α^n x_n` on finite histories. -/
def semanticReader (α : ℝ) : (ℕ →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ fun n => (α : ℂ) ^ n

/-- The genealogy acting on finite histories. -/
def finiteHistoryGenealogy (α : ℝ) (l : ℕ →₀ ℂ) : ℕ →₀ ℂ :=
  l - (α : ℂ) • Finsupp.comapDomain (fun n => n + 1) l
    ((add_left_injective 1).injOn)

theorem finiteHistoryGenealogy_apply (α : ℝ) (l : ℕ →₀ ℂ) (n : ℕ) :
    finiteHistoryGenealogy α l n = l n - α * l (n + 1) := by
  simp [finiteHistoryGenealogy, Finsupp.comapDomain_apply]

theorem finiteHistory_finiteHistoryGenealogy (α : ℝ) (l : ℕ →₀ ℂ) :
    finiteHistory (finiteHistoryGenealogy α l) = cofinalGenealogy α (finiteHistory l) := by
  ext n
  rw [finiteHistory_apply, finiteHistoryGenealogy_apply, cofinalGenealogy_apply,
    finiteHistory_apply, finiteHistory_apply]

theorem semanticReader_eq_sum_range (α : ℝ) (l : ℕ →₀ ℂ) {M : ℕ}
    (hM : l.support ⊆ Finset.range M) :
    semanticReader α l = ∑ n ∈ Finset.range M, (α : ℂ) ^ n * l n := by
  rw [semanticReader, Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset l hM]
  · exact Finset.sum_congr rfl fun n _ => by rw [smul_eq_mul, mul_comm]
  · intro n _; rw [zero_smul]

/-- **(GR.18)** Semantic conservation in every chamber: `b_α G_α z = z_0`. -/
theorem semanticReader_finiteHistoryGenealogy (α : ℝ) (l : ℕ →₀ ℂ) :
    semanticReader α (finiteHistoryGenealogy α l) = l 0 := by
  classical
  obtain ⟨M, hM⟩ : ∃ M, l.support ⊆ Finset.range M :=
    ⟨l.support.sup id + 1, fun n hn => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))⟩
  have hM' : (finiteHistoryGenealogy α l).support ⊆ Finset.range M := by
    intro n hn
    rw [Finsupp.mem_support_iff, finiteHistoryGenealogy_apply] at hn
    by_contra hnot
    rw [Finset.mem_range, not_lt] at hnot
    have h1 : l n = 0 := Finsupp.notMem_support_iff.mp fun h =>
      (Finset.mem_range.mp (hM h)).not_ge hnot
    have h2 : l (n + 1) = 0 := Finsupp.notMem_support_iff.mp fun h =>
      (Finset.mem_range.mp (hM h)).not_ge (by omega)
    exact hn (by rw [h1, h2]; ring)
  have hlM : l M = 0 := Finsupp.notMem_support_iff.mp fun h =>
    (Finset.mem_range.mp (hM h)).false
  rw [semanticReader_eq_sum_range α _ hM']
  simp_rw [finiteHistoryGenealogy_apply]
  have htel := Finset.sum_range_sub' (fun n => (α : ℂ) ^ n * l n) M
  rw [hlM, mul_zero, sub_zero, pow_zero, one_mul] at htel
  rw [← htel]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [pow_succ]
  ring

theorem finiteHistory_initial (N : ℕ) :
    finiteHistory (∑ n ∈ Finset.range (N + 1), Finsupp.single n (1 : ℂ)) = initialBlock N := by
  ext k
  rw [finiteHistory_apply, initialBlock_apply, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_range]

/-- **Theorem 4.1** For `α ≥ 0`, the semantic reader extends continuously to `ℓ²` exactly when
`α < 1`. -/
theorem exists_continuous_semanticReader_iff {α : ℝ} (h0 : 0 ≤ α) :
    (∃ f : ToeplitzSpace →L[ℂ] ℂ, ∀ l : ℕ →₀ ℂ, f (finiteHistory l) = semanticReader α l) ↔
      α < 1 := by
  constructor
  · rintro ⟨f, hf⟩
    by_contra hge
    rw [not_lt] at hge
    obtain ⟨N, hN⟩ := exists_nat_gt (‖f‖ ^ 2)
    set l : ℕ →₀ ℂ := ∑ n ∈ Finset.range (N + 1), Finsupp.single n (1 : ℂ)
    have hsupp : l.support ⊆ Finset.range (N + 1) := by
      intro n hn
      by_contra hnot
      apply Finsupp.mem_support_iff.mp hn
      rw [Finsupp.finsetSum_apply]
      exact Finset.sum_eq_zero fun m hm => by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl; exact hnot hm
    have hval : semanticReader α l = ∑ n ∈ Finset.range (N + 1), (α : ℂ) ^ n := by
      rw [semanticReader_eq_sum_range α l hsupp]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finsupp.finsetSum_apply, Finset.sum_eq_single n]
      · simp
      · intro m _ hmn; rw [Finsupp.single_apply, if_neg hmn]
      · intro h; exact absurd hn h
    have hreal : ∑ n ∈ Finset.range (N + 1), (α : ℂ) ^ n =
        ((∑ n ∈ Finset.range (N + 1), α ^ n : ℝ) : ℂ) := by push_cast; rfl
    have hlow : (N + 1 : ℝ) ≤ ∑ n ∈ Finset.range (N + 1), α ^ n := by
      calc (N + 1 : ℝ) = ∑ n ∈ Finset.range (N + 1), (1 : ℝ) := by simp
        _ ≤ ∑ n ∈ Finset.range (N + 1), α ^ n :=
            Finset.sum_le_sum fun n _ => one_le_pow₀ hge
    have hupper : ‖f (finiteHistory l)‖ ≤ ‖f‖ * Real.sqrt (N + 1 : ℝ) := by
      calc ‖f (finiteHistory l)‖ ≤ ‖f‖ * ‖finiteHistory l‖ := f.le_opNorm _
        _ = ‖f‖ * Real.sqrt (N + 1 : ℝ) := by
            rw [finiteHistory_initial, ← Real.sqrt_sq (norm_nonneg (initialBlock N)),
              norm_sq_initialBlock]
    rw [hf, hval, hreal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)] at hupper
    have hs : 0 < Real.sqrt (N + 1 : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hsq : Real.sqrt (N + 1 : ℝ) ^ 2 = N + 1 := Real.sq_sqrt (by positivity)
    have hkey : Real.sqrt (N + 1 : ℝ) ≤ ‖f‖ := by nlinarith
    have : (N + 1 : ℝ) ≤ ‖f‖ ^ 2 := by
      rw [← hsq]; exact pow_le_pow_left₀ hs.le hkey 2
    linarith
  · intro h1
    have hsum : Summable fun n : ℕ => ‖((α ^ n : ℝ) : ℂ)‖ ^ 2 := by
      have hr : α ^ 2 < 1 := pow_lt_one₀ h0 h1 two_ne_zero
      refine (summable_geometric_of_lt_one (by positivity) hr).congr fun n => ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      ring
    let a : ToeplitzSpace := ⟨fun n => ((α ^ n : ℝ) : ℂ), memℓp_gen (by simpa using hsum)⟩
    refine ⟨innerSL ℂ a, fun l => ?_⟩
    obtain ⟨M, hM⟩ : ∃ M, l.support ⊆ Finset.range M :=
      ⟨l.support.sup id + 1, fun n hn => Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))⟩
    rw [innerSL_apply_apply, lp.inner_eq_tsum, semanticReader_eq_sum_range α l hM,
      tsum_eq_sum (s := Finset.range M)]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [finiteHistory_apply, RCLike.inner_apply]
      show l n * (starRingEnd ℂ) ((α ^ n : ℝ) : ℂ) = _
      rw [Complex.conj_ofReal]
      push_cast
      ring
    · intro n hn
      rw [finiteHistory_apply, Finsupp.notMem_support_iff.mp (fun h => hn (hM h)),
        inner_zero_right]

/-! ## Compact repair -/

/-- Joint lower bound for the observer `x ↦ (A x, G x)` (GR.19). -/
def JointlyBoundedBelow {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (A : ToeplitzSpace →L[ℂ] Y) (G : ToeplitzSpace →L[ℂ] ToeplitzSpace) : Prop :=
  ∃ c > 0, ∀ x, c * ‖x‖ ≤ ‖A x‖ + ‖G x‖

/-- **Theorem 5.1(1)** In the subcritical chamber every observer is repaired. -/
theorem jointlyBoundedBelow_subcritical {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (A : ToeplitzSpace →L[ℂ] Y) :
    JointlyBoundedBelow A (cofinalGenealogy α) :=
  ⟨1 - α, by linarith, fun x =>
    (cofinalGenealogy_boundedBelow h0 h1 x).trans (le_add_of_nonneg_left (norm_nonneg _))⟩

/-- A compact operator from `ℓ²` to any normed space sends a bounded weakly-null sequence to
zero. -/
theorem tendsto_compactOperator_of_weaklyNull {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] (A : ToeplitzSpace →L[ℂ] Y) (hA : IsCompactOperator A)
    (x : ℕ → ToeplitzSpace) (hb : ∀ n, ‖x n‖ ≤ 1)
    (hweak : ∀ z, Tendsto (fun n => ⟪z, x n⟫_ℂ) atTop (𝓝 0)) :
    Tendsto (fun n => A (x n)) atTop (𝓝 0) := by
  have hfun : ∀ φ : Y →L[ℂ] ℂ, Tendsto (fun n => φ (A (x n))) atTop (𝓝 0) := by
    intro φ
    set z := (InnerProductSpace.toDual ℂ ToeplitzSpace).symm (φ ∘L A)
    have hz : ∀ n, φ (A (x n)) = ⟪z, x n⟫_ℂ := by
      intro n
      rw [InnerProductSpace.toDual_symm_apply]
      rfl
    simp_rw [hz]
    exact hweak z
  by_contra hne
  rw [Metric.tendsto_atTop] at hne
  simp only [not_forall, not_exists, not_lt] at hne
  obtain ⟨ε, hε, hfreq⟩ := hne
  have hfreq' : ∃ᶠ n in atTop, ε ≤ ‖A (x n)‖ := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hn, h⟩ := hfreq N
    exact ⟨n, hn, by simpa using h⟩
  obtain ⟨φs, hmono, hφ⟩ := Filter.extraction_of_frequently_atTop hfreq'
  have hK := hA.isCompact_closure_image_closedBall 1
  have hmem : ∀ k, A (x (φs k)) ∈ closure (A '' Metric.closedBall 0 1) := fun k =>
    subset_closure ⟨x (φs k), by simpa using hb (φs k), rfl⟩
  obtain ⟨y, -, ψ, hψ, hlim⟩ := hK.tendsto_subseq hmem
  have hy : ε ≤ ‖y‖ :=
    ge_of_tendsto ((continuous_norm.tendsto y).comp hlim)
      (Eventually.of_forall fun k => hφ (ψ k))
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy; linarith
  obtain ⟨g, -, hgy⟩ := exists_dual_vector ℂ y (norm_ne_zero_iff.mpr hy0)
  have h1 := (hfun g).comp (hmono.comp hψ).tendsto_atTop
  have h2 := (g.continuous.tendsto y).comp hlim
  have hzero : g y = 0 := tendsto_nhds_unique h2 h1
  rw [hgy] at hzero
  have : ‖y‖ = 0 := (RCLike.ofReal_eq_zero (K := ℂ)).mp hzero
  exact hy0 (norm_eq_zero.mp this)

theorem criticalHistory_apply (N k : ℕ) :
    (criticalHistory N : ℕ → ℂ) k =
      ((Real.sqrt (N + 1 : ℝ))⁻¹ : ℂ) * (if k ≤ N then 1 else 0) := by
  rw [criticalHistory, lp.coeFn_smul, Pi.smul_apply, initialBlock_apply, smul_eq_mul]

/-- The critical unit histories are weakly null. -/
theorem criticalHistory_weaklyNull (z : ToeplitzSpace) :
    Tendsto (fun N => ⟪z, criticalHistory N⟫_ℂ) atTop (𝓝 0) := by
  apply tendsto_inner_lp_of_coord (C := 1) criticalHistory zero_le_one
    (fun N => (norm_criticalHistory N).le)
  intro k
  have hsqrt : Tendsto (fun N : ℕ => ((Real.sqrt (N + 1 : ℝ))⁻¹ : ℂ)) atTop (𝓝 0) := by
    have h : Tendsto (fun N : ℕ => (Real.sqrt (N + 1 : ℝ))⁻¹) atTop (𝓝 0) := by
      have := tendsto_norm_cofinalGenealogy_one_criticalHistory
      simpa only [norm_cofinalGenealogy_one_criticalHistory] using this
    have := (Complex.continuous_ofReal.tendsto 0).comp h
    rw [Complex.ofReal_zero] at this
    refine this.congr fun N => ?_
    simp
  refine hsqrt.congr' ?_
  filter_upwards [eventually_ge_atTop k] with N hN
  rw [criticalHistory_apply, if_pos hN, mul_one]

/-- **Theorem 5.1(2)** At the critical wall no compact observer repairs the genealogy. -/
theorem not_jointlyBoundedBelow_critical {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (A : ToeplitzSpace →L[ℂ] Y) (hA : IsCompactOperator A) :
    ¬ JointlyBoundedBelow A (cofinalGenealogy 1) := by
  rintro ⟨c, hc, h⟩
  have hA0 := tendsto_compactOperator_of_weaklyNull A hA criticalHistory
    (fun N => (norm_criticalHistory N).le) criticalHistory_weaklyNull
  have hsum : Tendsto (fun N => ‖A (criticalHistory N)‖ +
      ‖cofinalGenealogy 1 (criticalHistory N)‖) atTop (𝓝 0) := by
    have := (tendsto_norm_zero.comp hA0).add
      tendsto_norm_cofinalGenealogy_one_criticalHistory
    simpa using this
  obtain ⟨N, hN⟩ := (hsum.eventually (gt_mem_nhds hc)).exists
  have := h (criticalHistory N)
  rw [norm_criticalHistory, mul_one] at this
  linarith

/-- The orthogonal complement of the hidden lineage. -/
abbrev hiddenLineageComplement {α : ℝ} (hα : 1 < α) : Submodule ℂ ToeplitzSpace :=
  (ℂ ∙ hiddenLineage hα)ᗮ

/-- The genealogy restricted to the complement of the hidden lineage. -/
def restrictedGenealogy {α : ℝ} (hα : 1 < α) :
    hiddenLineageComplement hα →L[ℂ] ToeplitzSpace :=
  cofinalGenealogy α ∘L (hiddenLineageComplement hα).subtypeL

theorem hiddenLineage_decomposition {α : ℝ} (hα : 1 < α) (x : ToeplitzSpace) :
    x - (⟪hiddenLineage hα, x⟫_ℂ / (‖hiddenLineage hα‖ ^ 2 : ℝ)) • hiddenLineage hα ∈
      hiddenLineageComplement hα := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right]
  have hg : ‖hiddenLineage hα‖ ≠ 0 := norm_ne_zero_iff.mpr (hiddenLineage_ne_zero hα)
  have hgg : ⟪hiddenLineage hα, hiddenLineage hα⟫_ℂ = ((‖hiddenLineage hα‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hgg, div_mul_cancel₀ _ (by exact_mod_cast pow_ne_zero 2 hg), sub_self]

theorem restrictedGenealogy_bijective {α : ℝ} (hα : 1 < α) :
    Function.Bijective (restrictedGenealogy hα) := by
  constructor
  · intro u v huv
    have huv' : cofinalGenealogy α (u : ToeplitzSpace) = cofinalGenealogy α v := huv
    have hsub : cofinalGenealogy α ((u : ToeplitzSpace) - v) = 0 := by
      rw [map_sub, huv', sub_self]
    have hker : (u : ToeplitzSpace) - v ∈ ℂ ∙ hiddenLineage hα := by
      rw [← ker_cofinalGenealogy hα]; exact hsub
    have hperp : (u : ToeplitzSpace) - v ∈ hiddenLineageComplement hα :=
      Submodule.sub_mem _ u.2 v.2
    have h0 := Submodule.inf_orthogonal_eq_bot (ℂ ∙ hiddenLineage hα)
    have : (u : ToeplitzSpace) - v ∈ (ℂ ∙ hiddenLineage hα) ⊓ (ℂ ∙ hiddenLineage hα)ᗮ :=
      ⟨hker, hperp⟩
    rw [h0, Submodule.mem_bot, sub_eq_zero] at this
    exact Subtype.ext this
  · intro y
    obtain ⟨x, rfl⟩ := cofinalGenealogy_surjective hα y
    refine ⟨⟨_, hiddenLineage_decomposition hα x⟩, ?_⟩
    change cofinalGenealogy α (x - _ • hiddenLineage hα) = cofinalGenealogy α x
    rw [map_sub, map_smul, cofinalGenealogy_hiddenLineage, smul_zero, sub_zero]

/-- The bounded inverse `J_α` of the genealogy on the complement of the hidden lineage. -/
def genealogyComplementInverse {α : ℝ} (hα : 1 < α) : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  (hiddenLineageComplement hα).subtypeL ∘L
    ((ContinuousLinearEquiv.ofBijective (restrictedGenealogy hα)
      (LinearMap.ker_eq_bot.mpr (restrictedGenealogy_bijective hα).1)
      (LinearMap.range_eq_top.mpr (restrictedGenealogy_bijective hα).2)).symm :
        ToeplitzSpace →L[ℂ] hiddenLineageComplement hα)

/-- The compact rank-one observer `A_α x = ⟨g_α, x⟩ / ‖g_α‖` (GR.21). -/
def hiddenLineageObserver {α : ℝ} (hα : 1 < α) : ToeplitzSpace →L[ℂ] ℂ :=
  ((‖hiddenLineage hα‖⁻¹ : ℝ) : ℂ) • innerSL ℂ (hiddenLineage hα)

/-- **(GR.22)** Exact joint reconstruction:
`x = J_α(G_α x) + (A_α x / ‖g_α‖) g_α`. -/
theorem jointReconstruction {α : ℝ} (hα : 1 < α) (x : ToeplitzSpace) :
    x = genealogyComplementInverse hα (cofinalGenealogy α x) +
      (hiddenLineageObserver hα x / (‖hiddenLineage hα‖ : ℂ)) • hiddenLineage hα := by
  set e := ContinuousLinearEquiv.ofBijective (restrictedGenealogy hα)
    (LinearMap.ker_eq_bot.mpr (restrictedGenealogy_bijective hα).1)
    (LinearMap.range_eq_top.mpr (restrictedGenealogy_bijective hα).2)
  set u : hiddenLineageComplement hα := ⟨_, hiddenLineage_decomposition hα x⟩
  have hGu : restrictedGenealogy hα u = cofinalGenealogy α x := by
    change cofinalGenealogy α (x - _ • hiddenLineage hα) = cofinalGenealogy α x
    rw [map_sub, map_smul, cofinalGenealogy_hiddenLineage, smul_zero, sub_zero]
  have hJ : genealogyComplementInverse hα (cofinalGenealogy α x) = (u : ToeplitzSpace) := by
    change ((e.symm (cofinalGenealogy α x) : hiddenLineageComplement hα) : ToeplitzSpace) = u
    rw [← hGu]
    change ((e.symm (e u) : hiddenLineageComplement hα) : ToeplitzSpace) = u
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [hJ]
  have hg : ‖hiddenLineage hα‖ ≠ 0 := norm_ne_zero_iff.mpr (hiddenLineage_ne_zero hα)
  have hcoef : hiddenLineageObserver hα x / (‖hiddenLineage hα‖ : ℂ) =
      ⟪hiddenLineage hα, x⟫_ℂ / (‖hiddenLineage hα‖ ^ 2 : ℝ) := by
    rw [hiddenLineageObserver, FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply, smul_eq_mul]
    have hgc : ((‖hiddenLineage hα‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hg
    push_cast
    field_simp
  rw [hcoef]
  change x = (x - _ • hiddenLineage hα) + _
  abel

theorem hiddenLineageObserver_hiddenLineage {α : ℝ} (hα : 1 < α) :
    hiddenLineageObserver hα (hiddenLineage hα) = (‖hiddenLineage hα‖ : ℂ) := by
  have hg : ‖hiddenLineage hα‖ ≠ 0 := norm_ne_zero_iff.mpr (hiddenLineage_ne_zero hα)
  rw [hiddenLineageObserver, FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply,
    inner_self_eq_norm_sq_to_K, smul_eq_mul]
  have hgc : ((‖hiddenLineage hα‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hg
  push_cast
  field_simp
  rfl

/-- **Theorem 5.1(3)** Above the wall an observer repairs the genealogy exactly when it sees the
hidden lineage. -/
theorem jointlyBoundedBelow_supercritical_iff {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] {α : ℝ} (hα : 1 < α) (A : ToeplitzSpace →L[ℂ] Y) :
    JointlyBoundedBelow A (cofinalGenealogy α) ↔ A (hiddenLineage hα) ≠ 0 := by
  constructor
  · rintro ⟨c, hc, h⟩ hAg
    have := h (hiddenLineage hα)
    rw [hAg, cofinalGenealogy_hiddenLineage, norm_zero, norm_zero, add_zero] at this
    have hg : 0 < ‖hiddenLineage hα‖ := norm_pos_iff.mpr (hiddenLineage_ne_zero hα)
    nlinarith
  · intro hAg
    set g := hiddenLineage hα
    set J := genealogyComplementInverse hα
    have hAgpos : 0 < ‖A g‖ := norm_pos_iff.mpr hAg
    have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr (hiddenLineage_ne_zero hα)
    set C : ℝ := ‖J‖ + ‖g‖ * (1 + ‖A‖ * ‖J‖) / ‖A g‖ with hC
    have hCpos : 0 < C := by positivity
    refine ⟨C⁻¹, inv_pos.mpr hCpos, fun x => ?_⟩
    set t : ℂ := hiddenLineageObserver hα x / (‖g‖ : ℂ)
    have hrec := jointReconstruction hα x
    have hAx : A x = A (J (cofinalGenealogy α x)) + t • A g := by
      conv_lhs => rw [hrec]
      rw [map_add, map_smul]
    have ht : ‖t‖ * ‖A g‖ ≤ ‖A x‖ + ‖A‖ * ‖J‖ * ‖cofinalGenealogy α x‖ := by
      have h1 : t • A g = A x - A (J (cofinalGenealogy α x)) := by rw [hAx]; abel
      have h2 : ‖A (J (cofinalGenealogy α x))‖ ≤ ‖A‖ * ‖J‖ * ‖cofinalGenealogy α x‖ := by
        calc ‖A (J (cofinalGenealogy α x))‖ ≤ ‖A‖ * ‖J (cofinalGenealogy α x)‖ := A.le_opNorm _
          _ ≤ ‖A‖ * (‖J‖ * ‖cofinalGenealogy α x‖) :=
              mul_le_mul_of_nonneg_left (J.le_opNorm _) (norm_nonneg _)
          _ = _ := by ring
      calc ‖t‖ * ‖A g‖ = ‖t • A g‖ := (norm_smul _ _).symm
        _ = ‖A x - A (J (cofinalGenealogy α x))‖ := by rw [h1]
        _ ≤ ‖A x‖ + ‖A (J (cofinalGenealogy α x))‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    have hx : ‖x‖ ≤ ‖J‖ * ‖cofinalGenealogy α x‖ + ‖t‖ * ‖g‖ := by
      calc ‖x‖ = ‖J (cofinalGenealogy α x) + t • g‖ := by rw [← hrec]
        _ ≤ ‖J (cofinalGenealogy α x)‖ + ‖t • g‖ := norm_add_le _ _
        _ ≤ ‖J‖ * ‖cofinalGenealogy α x‖ + ‖t‖ * ‖g‖ := by
            rw [norm_smul]; exact add_le_add (J.le_opNorm _) le_rfl
    have htle : ‖t‖ ≤ (‖A x‖ + ‖A‖ * ‖J‖ * ‖cofinalGenealogy α x‖) / ‖A g‖ := by
      rw [le_div_iff₀ hAgpos]; exact ht
    rw [inv_mul_eq_div, div_le_iff₀ hCpos]
    have hGx := norm_nonneg (cofinalGenealogy α x)
    have hAx0 := norm_nonneg (A x)
    have hkey : ‖x‖ ≤ ‖J‖ * ‖cofinalGenealogy α x‖ +
        (‖A x‖ + ‖A‖ * ‖J‖ * ‖cofinalGenealogy α x‖) / ‖A g‖ * ‖g‖ :=
      hx.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right htle hgpos.le))
    calc ‖x‖ ≤ ‖J‖ * ‖cofinalGenealogy α x‖ +
          (‖A x‖ + ‖A‖ * ‖J‖ * ‖cofinalGenealogy α x‖) / ‖A g‖ * ‖g‖ := hkey
      _ ≤ (‖A x‖ + ‖cofinalGenealogy α x‖) * C := by
          have hJ0 := norm_nonneg J
          have hA0 := norm_nonneg A
          have hdiff : (‖A x‖ + ‖cofinalGenealogy α x‖) * C -
              (‖J‖ * ‖cofinalGenealogy α x‖ +
                (‖A x‖ + ‖A‖ * ‖J‖ * ‖cofinalGenealogy α x‖) / ‖A g‖ * ‖g‖) =
              ‖A x‖ * ‖J‖ + (‖A x‖ * ‖g‖ * ‖A‖ * ‖J‖ + ‖cofinalGenealogy α x‖ * ‖g‖) / ‖A g‖ := by
            rw [hC]
            field_simp
            ring
          have hnn : 0 ≤ ‖A x‖ * ‖J‖ +
              (‖A x‖ * ‖g‖ * ‖A‖ * ‖J‖ + ‖cofinalGenealogy α x‖ * ‖g‖) / ‖A g‖ := by positivity
          linarith

/-- **Theorem 5.1(3), rank-one repair.**  The compact rank-one observer `A_α` repairs the
supercritical genealogy. -/
theorem jointlyBoundedBelow_hiddenLineageObserver {α : ℝ} (hα : 1 < α) :
    IsCompactOperator (hiddenLineageObserver hα) ∧
      JointlyBoundedBelow (hiddenLineageObserver hα) (cofinalGenealogy α) := by
  refine ⟨isCompactOperator_of_locallyCompactSpace_dom (hiddenLineageObserver hα), ?_⟩
  rw [jointlyBoundedBelow_supercritical_iff hα, hiddenLineageObserver_hiddenLineage]
  exact_mod_cast norm_ne_zero_iff.mpr (hiddenLineage_ne_zero hα)

/-! ## Reciprocity, terminal ports, and index -/

/-- **(GR.23)** `G_α = -α B G_{1/α}^*`. -/
theorem cofinalGenealogy_reciprocal {α : ℝ} (hα : 0 < α) :
    cofinalGenealogy α = (-(α : ℂ)) • (backOp 1 ∘L adjoint (cofinalGenealogy α⁻¹)) := by
  rw [adjoint_cofinalGenealogy]
  exact cofinalGenealogy_eq_neg_smul_backOp_comp hα.ne'

/-- The terminal projection `P_N x = x_N e_N`. -/
def terminalPort (N : ℕ) : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  (innerSL ℂ (lp.single 2 N (1 : ℂ) : ToeplitzSpace)).smulRight
    (lp.single 2 N (1 : ℂ) : ToeplitzSpace)

theorem terminalPort_apply (N : ℕ) (x : ToeplitzSpace) :
    terminalPort N x = (x : ℕ → ℂ) N • (lp.single 2 N (1 : ℂ) : ToeplitzSpace) := by
  rw [terminalPort, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    lp.inner_single_left]
  simp

theorem norm_single_one (N : ℕ) : ‖(lp.single 2 N (1 : ℂ) : ToeplitzSpace)‖ = 1 := by
  rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one]

/-- The terminal ports have norm one. -/
theorem norm_terminalPort (N : ℕ) : ‖terminalPort N‖ = 1 := by
  rw [terminalPort, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm,
    norm_single_one, one_mul]

/-- The terminal ports converge strongly to zero. -/
theorem tendsto_terminalPort (x : ToeplitzSpace) :
    Tendsto (fun N => terminalPort N x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_norm_zero.comp (tendsto_toeplitz_coord x)
  refine h.congr fun N => ?_
  simp [terminalPort_apply, norm_smul]

/-- Fredholm index `dim ker - dim coker` (meaningful for Fredholm operators). -/
def genealogyFredholmIndex (T : ToeplitzSpace →L[ℂ] ToeplitzSpace) : ℤ :=
  (Module.finrank ℂ (LinearMap.ker (T : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace)) : ℤ) -
    Module.finrank ℂ (LinearMap.range (T : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace))ᗮ

/-- **(GR.25)** Subcritical chamber: Fredholm of index zero. -/
theorem cofinalGenealogy_fredholm_subcritical {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    IsBoundedFredholm (cofinalGenealogy α) ∧ genealogyFredholmIndex (cofinalGenealogy α) = 0 := by
  have hu := cofinalGenealogy_isUnit h0 h1
  have hbij : Function.Bijective (cofinalGenealogy α) := by
    obtain ⟨u, hu⟩ := hu
    rw [← hu]
    exact ⟨fun a b h => by
        have := congrArg (fun y => (u⁻¹ : (ToeplitzSpace →L[ℂ] ToeplitzSpace)ˣ).val y) h
        simpa [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def] using this,
      fun y => ⟨(u⁻¹ : (ToeplitzSpace →L[ℂ] ToeplitzSpace)ˣ).val y, by
        have := congrArg (fun T : ToeplitzSpace →L[ℂ] ToeplitzSpace => T y) u.mul_inv
        exact this⟩⟩
  have hker : LinearMap.ker (cofinalGenealogy α : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hbij.1
  have hran : LinearMap.range (cofinalGenealogy α : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace) = ⊤ :=
    LinearMap.range_eq_top.mpr hbij.2
  have hclosed : IsClosed (Set.range (cofinalGenealogy α)) := by
    rw [Set.range_eq_univ.mpr hbij.2]; exact isClosed_univ
  refine ⟨⟨⟨hclosed, ?_⟩, ⟨hclosed, ?_⟩⟩, ?_⟩
  · rw [hker]; infer_instance
  · rw [hran, Submodule.top_orthogonal_eq_bot]; infer_instance
  · rw [genealogyFredholmIndex, hker, hran, Submodule.top_orthogonal_eq_bot]
    simp

/-- **(GR.25)** Critical chamber: not Fredholm. -/
theorem cofinalGenealogy_one_not_fredholm : ¬ IsBoundedFredholm (cofinalGenealogy 1) := by
  rintro ⟨⟨hcl, -⟩, -⟩
  exact not_isClosed_range_cofinalGenealogy_one hcl

/-- **(GR.25)** Supercritical chamber: Fredholm of index one. -/
theorem cofinalGenealogy_fredholm_supercritical {α : ℝ} (hα : 1 < α) :
    IsBoundedFredholm (cofinalGenealogy α) ∧ genealogyFredholmIndex (cofinalGenealogy α) = 1 := by
  have hsurj := cofinalGenealogy_surjective hα
  have hran : LinearMap.range (cofinalGenealogy α : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hclosed : IsClosed (Set.range (cofinalGenealogy α)) := by
    rw [Set.range_eq_univ.mpr hsurj]; exact isClosed_univ
  refine ⟨⟨⟨hclosed, ?_⟩, ⟨hclosed, ?_⟩⟩, ?_⟩
  · rw [ker_cofinalGenealogy hα]; infer_instance
  · rw [hran, Submodule.top_orthogonal_eq_bot]; infer_instance
  · rw [genealogyFredholmIndex, ker_cofinalGenealogy hα, hran, Submodule.top_orthogonal_eq_bot,
      finrank_bot, finrank_span_singleton (hiddenLineage_ne_zero hα)]
    rfl

end

end GaloisForLFunctions.HTGeometry
