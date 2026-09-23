import GaloisForLFunctions.RHTower.BoundaryWeylThresholdNonMonotone

/-!
# A pole budget does not force the Uvarov repair

For two boundary functionals that are not scalar multiples, pick `q` with `α q = 1` and `β q = 0`.
The Hermitian form

`A v = -‖α v‖ ^ (2 : ℕ) + ‖v - (α v) • q‖ ^ (2 : ℕ)`

is positive definite on `ker α`, has its single negative direction at `q`, and for every `c > 1`
decomposes as `A = R - c α* α` with `R` positive definite.  Yet

`(A + t β* β) q = -1 < 0`

for every `t`, because `q` is invisible to `β`.

So the pole-channel structure "positive bulk minus one rank-one pole square" does not by itself
force positivity after a rank-one repair at a different boundary point.
-/

noncomputable section

namespace RHTower

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The pole-budget form with one negative direction at `q`. -/
def poleBudgetForm (α : V →ₗ[ℂ] ℂ) (q : V) (v : V) : ℝ :=
  -‖α v‖ ^ (2 : ℕ) + ‖v - (α v) • q‖ ^ (2 : ℕ)

/-- Its positive-definite completion after adding back `c` pole squares. -/
def poleBudgetPositivePart (α : V →ₗ[ℂ] ℂ) (q : V) (c : ℝ) (v : V) : ℝ :=
  (c - 1) * ‖α v‖ ^ (2 : ℕ) + ‖v - (α v) • q‖ ^ (2 : ℕ)

/-- **Exact pole decomposition** `A = R - c α* α`. -/
theorem poleBudget_decomposition (α : V →ₗ[ℂ] ℂ) (q : V) (c : ℝ) (v : V) :
    poleBudgetForm α q v = poleBudgetPositivePart α q c v - c * ‖α v‖ ^ (2 : ℕ) := by
  unfold poleBudgetForm poleBudgetPositivePart
  ring

/-- **Positivity on the pole kernel.** -/
theorem poleBudgetForm_pos_on_ker (α : V →ₗ[ℂ] ℂ) (q : V) {v : V} (hv : v ≠ 0)
    (hker : α v = 0) : 0 < poleBudgetForm α q v := by
  unfold poleBudgetForm
  rw [hker]
  simp only [norm_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, neg_zero,
    zero_smul, sub_zero, zero_add]
  have : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  positivity

/-- **The single negative direction.** -/
theorem poleBudgetForm_at_q (α : V →ₗ[ℂ] ℂ) {q : V} (hαq : α q = 1) :
    poleBudgetForm α q q = -1 := by
  unfold poleBudgetForm
  rw [hαq]
  simp

/-- **The completion is positive definite.** -/
theorem poleBudgetPositivePart_pos (α : V →ₗ[ℂ] ℂ) {q : V} {c : ℝ} (hc : 1 < c)
    {v : V} (hv : v ≠ 0) : 0 < poleBudgetPositivePart α q c v := by
  unfold poleBudgetPositivePart
  by_cases hα : α v = 0
  · rw [hα]
    simp only [norm_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero,
      zero_smul, sub_zero, zero_add]
    have : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    positivity
  · have hpos : 0 < ‖α v‖ := norm_pos_iff.mpr hα
    have h1 : 0 < (c - 1) * ‖α v‖ ^ (2 : ℕ) := by
      have : 0 < c - 1 := by linarith
      positivity
    have h2 : 0 ≤ ‖v - (α v) • q‖ ^ (2 : ℕ) := sq_nonneg _
    linarith

/-- **The repair fails.**  The negative direction is invisible to the second boundary functional,
so no amount of rank-one repair there restores positivity. -/
theorem uvarov_repair_fails (α β : V →ₗ[ℂ] ℂ) {q : V} (hαq : α q = 1) (hβq : β q = 0) (t : ℝ) :
    poleBudgetForm α q q + t * ‖β q‖ ^ (2 : ℕ) = -1 := by
  rw [poleBudgetForm_at_q α hαq, hβq]
  simp

/-- **Pole budget does not imply Uvarov repair.**  The four clauses of the card, for any pair of
non-proportional boundary functionals. -/
theorem poleBudget_not_uvarov (α β : V →ₗ[ℂ] ℂ) {q : V} (hαq : α q = 1) (hβq : β q = 0)
    {c : ℝ} (hc : 1 < c) :
    poleBudgetForm α q q < 0 ∧
      (∀ v : V, v ≠ 0 → α v = 0 → 0 < poleBudgetForm α q v) ∧
      (∀ v : V, poleBudgetForm α q v = poleBudgetPositivePart α q c v - c * ‖α v‖ ^ (2 : ℕ)) ∧
      (∀ v : V, v ≠ 0 → 0 < poleBudgetPositivePart α q c v) ∧
      (∀ t : ℝ, poleBudgetForm α q q + t * ‖β q‖ ^ (2 : ℕ) < 0) := by
  refine ⟨?_, fun v hv hker => poleBudgetForm_pos_on_ker α q hv hker,
    fun v => poleBudget_decomposition α q c v,
    fun v hv => poleBudgetPositivePart_pos α hc hv, fun t => ?_⟩
  · rw [poleBudgetForm_at_q α hαq]
    norm_num
  · rw [uvarov_repair_fails α β hαq hβq t]
    norm_num

/-! ### The degree-one polynomial specialization -/

/-- Evaluation of a degree-`≤ 1` polynomial, presented by its coefficient pair. -/
def evalFunctional (y : ℂ) : (ℂ × ℂ) →ₗ[ℂ] ℂ where
  toFun p := p.1 + p.2 * y
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  map_smul' a p := by
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_eq_mul]
    ring

theorem evalFunctional_apply (y : ℂ) (p : ℂ × ℂ) : evalFunctional y p = p.1 + p.2 * y := rfl

/-- Two evaluation functionals at distinct points are not scalar multiples. -/
theorem evalFunctional_not_proportional {y z : ℂ} (hyz : y ≠ z) (c : ℂ) :
    evalFunctional y ≠ c • evalFunctional z := by
  intro h
  have h1 := congrArg (fun f : (ℂ × ℂ) →ₗ[ℂ] ℂ => f (1, 0)) h
  have h2 := congrArg (fun f : (ℂ × ℂ) →ₗ[ℂ] ℂ => f (0, 1)) h
  simp only [evalFunctional_apply, LinearMap.smul_apply, smul_eq_mul] at h1 h2
  norm_num at h1 h2
  rw [← h1] at h2
  simp at h2
  exact hyz h2

/-- The interpolating vector of the pole/first-trivial-zero pair. -/
def poleInterpolator (y z : ℂ) : ℂ × ℂ := ((-z) / (y - z), 1 / (y - z))

theorem evalFunctional_poleInterpolator_self {y z : ℂ} (hyz : y ≠ z) :
    evalFunctional y (poleInterpolator y z) = 1 := by
  rw [evalFunctional_apply, poleInterpolator]
  have hne : y - z ≠ 0 := sub_ne_zero.mpr hyz
  field_simp
  ring

theorem evalFunctional_poleInterpolator_other {y z : ℂ} (hyz : y ≠ z) :
    evalFunctional z (poleInterpolator y z) = 0 := by
  rw [evalFunctional_apply, poleInterpolator]
  have hne : y - z ≠ 0 := sub_ne_zero.mpr hyz
  field_simp
  ring

end RHTower
