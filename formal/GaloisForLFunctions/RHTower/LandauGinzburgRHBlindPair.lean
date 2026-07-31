import GaloisForLFunctions.RHTower.LandauGinzburgHolomorphicCore

/-!
# An exact pair of models the local vacuum data cannot separate

Write `z = s - 1/2`.  For positive `a, b, b₁, b₂` with `b₁ ≠ b₂` put

`onQuartic  = (z² + b₁²)(z² + b₂²)`,  `offQuartic = ((z - a)² + b²)((z + a)² + b²)`.

Both are real and even in `z`, so both satisfy the functional-equation reflection `s ↦ 1 - s` and
Schwarz reality.  Both have four simple zeros.  Every zero of `onQuartic` has real part `1/2` and no
zero of `offQuartic` does.  Nevertheless, at every zero of either model the multiplier potential has
the same local matrix-factorization category — the node's — so the two models have identical local
vacuum data.

* `linearQuartic` and its derivative at each root — a quartic with prescribed roots.
* `onQuartic`, `offQuartic`, their factorizations, reflection and reality.
* `onQuartic_re_eq`, `offQuartic_re_ne` — the on/off-line separation of the two zero sets.
* `onQuartic_deriv_ne_zero`, `offQuartic_deriv_ne_zero` — all eight zeros are simple.
* `rhBlind_localMatrixFactorization_equiv` — the local categories at any zero of either model agree.
-/

namespace GaloisForLFunctions.RHTower

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Quartics with prescribed roots -/

/-- The quartic with the four prescribed roots. -/
def linearQuartic (r₀ r₁ r₂ r₃ : ℂ) : ℂ → ℂ :=
  fun s => (s - r₀) * (s - r₁) * (s - r₂) * (s - r₃)

theorem analyticAt_linearQuartic (r₀ r₁ r₂ r₃ ρ : ℂ) :
    AnalyticAt ℂ (linearQuartic r₀ r₁ r₂ r₃) ρ := by
  have hid : AnalyticAt ℂ (fun s : ℂ => s) ρ := analyticAt_id
  exact ((((hid.sub analyticAt_const).mul (hid.sub analyticAt_const)).mul
    (hid.sub analyticAt_const)).mul (hid.sub analyticAt_const))

theorem linearQuartic_eq_zero_iff (r₀ r₁ r₂ r₃ s : ℂ) :
    linearQuartic r₀ r₁ r₂ r₃ s = 0 ↔ s = r₀ ∨ s = r₁ ∨ s = r₂ ∨ s = r₃ := by
  simp only [linearQuartic, mul_eq_zero, sub_eq_zero, or_assoc]

/-- The derivative of a product with a simple linear factor is the cofactor at the root. -/
theorem deriv_linearFactor_mul {G : ℂ → ℂ} {ρ : ℂ} (hG : DifferentiableAt ℂ G ρ) :
    deriv (fun z => (z - ρ) * G z) ρ = G ρ := by
  have h : HasDerivAt (fun z : ℂ => (z - ρ) * G z) (1 * G ρ + (ρ - ρ) * deriv G ρ) ρ :=
    ((hasDerivAt_id ρ).sub_const ρ).mul hG.hasDerivAt
  simpa using h.deriv

theorem deriv_linearQuartic_root₀ (r₀ r₁ r₂ r₃ : ℂ) :
    deriv (linearQuartic r₀ r₁ r₂ r₃) r₀ = (r₀ - r₁) * ((r₀ - r₂) * (r₀ - r₃)) := by
  have hfun : linearQuartic r₀ r₁ r₂ r₃
      = fun z => (z - r₀) * ((z - r₁) * ((z - r₂) * (z - r₃))) := by
    funext s
    simp only [linearQuartic]
    ring
  have hG : DifferentiableAt ℂ (fun z : ℂ => (z - r₁) * ((z - r₂) * (z - r₃))) r₀ := by
    fun_prop
  rw [hfun, deriv_linearFactor_mul hG]

theorem linearQuartic_swap₁ (r₀ r₁ r₂ r₃ : ℂ) :
    linearQuartic r₀ r₁ r₂ r₃ = linearQuartic r₁ r₀ r₂ r₃ := by
  funext s
  simp only [linearQuartic]
  ring

theorem linearQuartic_swap₂ (r₀ r₁ r₂ r₃ : ℂ) :
    linearQuartic r₀ r₁ r₂ r₃ = linearQuartic r₂ r₀ r₁ r₃ := by
  funext s
  simp only [linearQuartic]
  ring

theorem linearQuartic_swap₃ (r₀ r₁ r₂ r₃ : ℂ) :
    linearQuartic r₀ r₁ r₂ r₃ = linearQuartic r₃ r₀ r₁ r₂ := by
  funext s
  simp only [linearQuartic]
  ring

/-- **Every root of a quartic with four distinct prescribed roots is simple.** -/
theorem deriv_linearQuartic_ne_zero {r₀ r₁ r₂ r₃ ρ : ℂ}
    (h01 : r₀ ≠ r₁) (h02 : r₀ ≠ r₂) (h03 : r₀ ≠ r₃)
    (h12 : r₁ ≠ r₂) (h13 : r₁ ≠ r₃) (h23 : r₂ ≠ r₃)
    (hρ : linearQuartic r₀ r₁ r₂ r₃ ρ = 0) :
    deriv (linearQuartic r₀ r₁ r₂ r₃) ρ ≠ 0 := by
  have hmul : ∀ x y z : ℂ, x ≠ 0 → y ≠ 0 → z ≠ 0 → x * (y * z) ≠ 0 := by
    intro x y z hx hy hz
    exact mul_ne_zero hx (mul_ne_zero hy hz)
  rcases (linearQuartic_eq_zero_iff r₀ r₁ r₂ r₃ ρ).mp hρ with rfl | rfl | rfl | rfl
  · rw [deriv_linearQuartic_root₀]
    exact hmul _ _ _ (sub_ne_zero.mpr h01) (sub_ne_zero.mpr h02) (sub_ne_zero.mpr h03)
  · rw [linearQuartic_swap₁, deriv_linearQuartic_root₀]
    exact hmul _ _ _ (sub_ne_zero.mpr h01.symm) (sub_ne_zero.mpr h12) (sub_ne_zero.mpr h13)
  · rw [linearQuartic_swap₂, deriv_linearQuartic_root₀]
    exact hmul _ _ _ (sub_ne_zero.mpr h02.symm) (sub_ne_zero.mpr h12.symm) (sub_ne_zero.mpr h23)
  · rw [linearQuartic_swap₃, deriv_linearQuartic_root₀]
    exact hmul _ _ _ (sub_ne_zero.mpr h03.symm) (sub_ne_zero.mpr h13.symm) (sub_ne_zero.mpr h23.symm)

/-! ### The two models -/

/-- The on-line model `(z² + b₁²)(z² + b₂²)` in the variable `z = s - 1/2`. -/
def onQuartic (b₁ b₂ : ℝ) : ℂ → ℂ :=
  fun s => ((s - 1 / 2) ^ 2 + (b₁ : ℂ) ^ 2) * ((s - 1 / 2) ^ 2 + (b₂ : ℂ) ^ 2)

/-- The off-line model `((z - a)² + b²)((z + a)² + b²)` in the variable `z = s - 1/2`. -/
def offQuartic (a b : ℝ) : ℂ → ℂ :=
  fun s => (((s - 1 / 2) - (a : ℂ)) ^ 2 + (b : ℂ) ^ 2) *
    (((s - 1 / 2) + (a : ℂ)) ^ 2 + (b : ℂ) ^ 2)

theorem sq_add_sq_factor (z c : ℂ) : z ^ 2 + c ^ 2 = (z - I * c) * (z + I * c) := by
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  linear_combination (c ^ 2) * hI

theorem onQuartic_eq_linearQuartic (b₁ b₂ : ℝ) :
    onQuartic b₁ b₂ = linearQuartic (1 / 2 + I * b₁) (1 / 2 - I * b₁)
      (1 / 2 + I * b₂) (1 / 2 - I * b₂) := by
  funext s
  simp only [onQuartic, linearQuartic]
  rw [sq_add_sq_factor (s - 1 / 2) (b₁ : ℂ), sq_add_sq_factor (s - 1 / 2) (b₂ : ℂ)]
  ring

theorem offQuartic_eq_linearQuartic (a b : ℝ) :
    offQuartic a b = linearQuartic (1 / 2 + a + I * b) (1 / 2 + a - I * b)
      (1 / 2 - a + I * b) (1 / 2 - a - I * b) := by
  funext s
  simp only [offQuartic, linearQuartic]
  rw [sq_add_sq_factor ((s - 1 / 2) - (a : ℂ)) (b : ℂ),
    sq_add_sq_factor ((s - 1 / 2) + (a : ℂ)) (b : ℂ)]
  ring

theorem analyticAt_onQuartic (b₁ b₂ : ℝ) (ρ : ℂ) : AnalyticAt ℂ (onQuartic b₁ b₂) ρ := by
  rw [onQuartic_eq_linearQuartic]
  exact analyticAt_linearQuartic _ _ _ _ _

theorem analyticAt_offQuartic (a b : ℝ) (ρ : ℂ) : AnalyticAt ℂ (offQuartic a b) ρ := by
  rw [offQuartic_eq_linearQuartic]
  exact analyticAt_linearQuartic _ _ _ _ _

/-! ### Reflection and reality -/

/-- The on-line model is even in `z = s - 1/2`, hence obeys the functional-equation reflection. -/
theorem onQuartic_reflection (b₁ b₂ : ℝ) (s : ℂ) :
    onQuartic b₁ b₂ (1 - s) = onQuartic b₁ b₂ s := by
  simp only [onQuartic]
  ring

/-- The off-line model is even in `z = s - 1/2`, hence obeys the functional-equation reflection. -/
theorem offQuartic_reflection (a b : ℝ) (s : ℂ) :
    offQuartic a b (1 - s) = offQuartic a b s := by
  simp only [offQuartic]
  ring

/-- The on-line model is Schwarz real. -/
theorem onQuartic_conj (b₁ b₂ : ℝ) (s : ℂ) :
    onQuartic b₁ b₂ (starRingEnd ℂ s) = starRingEnd ℂ (onQuartic b₁ b₂ s) := by
  simp only [onQuartic, map_mul, map_add, map_pow, map_sub, map_div₀, map_one, map_ofNat,
    Complex.conj_ofReal]

/-- The off-line model is Schwarz real. -/
theorem offQuartic_conj (a b : ℝ) (s : ℂ) :
    offQuartic a b (starRingEnd ℂ s) = starRingEnd ℂ (offQuartic a b s) := by
  simp only [offQuartic, map_mul, map_add, map_pow, map_sub, map_div₀, map_one, map_ofNat,
    Complex.conj_ofReal]

/-! ### The zero sets -/

theorem onQuartic_eq_zero_iff (b₁ b₂ : ℝ) (s : ℂ) :
    onQuartic b₁ b₂ s = 0 ↔
      s = 1 / 2 + I * b₁ ∨ s = 1 / 2 - I * b₁ ∨ s = 1 / 2 + I * b₂ ∨ s = 1 / 2 - I * b₂ := by
  rw [onQuartic_eq_linearQuartic, linearQuartic_eq_zero_iff]

theorem offQuartic_eq_zero_iff (a b : ℝ) (s : ℂ) :
    offQuartic a b s = 0 ↔
      s = 1 / 2 + a + I * b ∨ s = 1 / 2 + a - I * b ∨
        s = 1 / 2 - a + I * b ∨ s = 1 / 2 - a - I * b := by
  rw [offQuartic_eq_linearQuartic, linearQuartic_eq_zero_iff]

/-- **Every zero of the on-line model lies on the critical line.** -/
theorem onQuartic_re_eq {b₁ b₂ : ℝ} {s : ℂ} (hs : onQuartic b₁ b₂ s = 0) : s.re = 1 / 2 := by
  rcases (onQuartic_eq_zero_iff b₁ b₂ s).mp hs with rfl | rfl | rfl | rfl <;>
    simp

/-- **No zero of the off-line model lies on the critical line.** -/
theorem offQuartic_re_ne {a b : ℝ} (ha : 0 < a) {s : ℂ} (hs : offQuartic a b s = 0) :
    s.re ≠ 1 / 2 := by
  rcases (offQuartic_eq_zero_iff a b s).mp hs with rfl | rfl | rfl | rfl <;>
    · simp
      linarith

/-! ### Simplicity of the eight zeros -/

theorem onQuartic_deriv_ne_zero {b₁ b₂ : ℝ} (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hne : b₁ ≠ b₂)
    {s : ℂ} (hs : onQuartic b₁ b₂ s = 0) : deriv (onQuartic b₁ b₂) s ≠ 0 := by
  have him : ∀ c : ℝ, ((1 : ℂ) / 2 + I * c).im = c := by intro c; simp
  have him' : ∀ c : ℝ, ((1 : ℂ) / 2 - I * c).im = -c := by intro c; simp
  rw [onQuartic_eq_linearQuartic] at hs ⊢
  refine deriv_linearQuartic_ne_zero ?_ ?_ ?_ ?_ ?_ ?_ hs
  · intro h; have := congrArg Complex.im h; rw [him, him'] at this; linarith
  · intro h; have := congrArg Complex.im h; rw [him, him] at this; exact hne this
  · intro h; have := congrArg Complex.im h; rw [him, him'] at this; linarith
  · intro h; have := congrArg Complex.im h; rw [him', him] at this; linarith
  · intro h; have := congrArg Complex.im h; rw [him', him'] at this
    exact hne (by linarith)
  · intro h; have := congrArg Complex.im h; rw [him, him'] at this; linarith

theorem offQuartic_deriv_ne_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {s : ℂ} (hs : offQuartic a b s = 0) : deriv (offQuartic a b) s ≠ 0 := by
  have hreP : ∀ c : ℝ, ((1 : ℂ) / 2 + a + I * c).re = 1 / 2 + a := by intro c; simp
  have hreM : ∀ c : ℝ, ((1 : ℂ) / 2 - a + I * c).re = 1 / 2 - a := by intro c; simp
  have himP : ∀ c : ℝ, ((1 : ℂ) / 2 + a + I * c).im = c := by intro c; simp
  have himM : ∀ c : ℝ, ((1 : ℂ) / 2 - a + I * c).im = c := by intro c; simp
  have hsubP : ((1 : ℂ) / 2 + a - I * b) = ((1 : ℂ) / 2 + a + I * (-b : ℝ)) := by
    push_cast; ring
  have hsubM : ((1 : ℂ) / 2 - a - I * b) = ((1 : ℂ) / 2 - a + I * (-b : ℝ)) := by
    push_cast; ring
  rw [offQuartic_eq_linearQuartic] at hs ⊢
  refine deriv_linearQuartic_ne_zero ?_ ?_ ?_ ?_ ?_ ?_ hs
  · intro h; rw [hsubP] at h
    have := congrArg Complex.im h; rw [himP, himP] at this; linarith
  · intro h; have := congrArg Complex.re h; rw [hreP, hreM] at this; linarith
  · intro h; rw [hsubM] at h
    have := congrArg Complex.re h; rw [hreP, hreM] at this; linarith
  · intro h; rw [hsubP] at h
    have := congrArg Complex.re h; rw [hreP, hreM] at this; linarith
  · intro h; rw [hsubP, hsubM] at h
    have := congrArg Complex.re h; rw [hreP, hreM] at this; linarith
  · intro h; rw [hsubM] at h
    have := congrArg Complex.im h; rw [himM, himM] at this; linarith

/-! ### The local categories agree -/

/-- Every zero of the on-line model carries the node's local matrix-factorization category. -/
theorem onQuartic_node_category {b₁ b₂ : ℝ} (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hne : b₁ ≠ b₂)
    {ρ : ℂ} (hρ : onQuartic b₁ b₂ ρ = 0) :
    Nonempty (MatrixFactorization (AnalyticGerm ((0 : ℂ), (0 : ℂ)))
        (analyticGermOf (analyticAt_nodePotential ((0 : ℂ), (0 : ℂ))))
      ≌ MatrixFactorization (AnalyticGerm (ρ, (0 : ℂ)))
        (analyticGermOf (analyticAt_lgPotential (analyticAt_onQuartic b₁ b₂ ρ)))) :=
  exists_lgNodeMatrixFactorizationEquiv (analyticAt_onQuartic b₁ b₂ ρ) hρ
    (onQuartic_deriv_ne_zero hb₁ hb₂ hne hρ)

/-- Every zero of the off-line model carries the node's local matrix-factorization category. -/
theorem offQuartic_node_category {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {ρ : ℂ} (hρ : offQuartic a b ρ = 0) :
    Nonempty (MatrixFactorization (AnalyticGerm ((0 : ℂ), (0 : ℂ)))
        (analyticGermOf (analyticAt_nodePotential ((0 : ℂ), (0 : ℂ))))
      ≌ MatrixFactorization (AnalyticGerm (ρ, (0 : ℂ)))
        (analyticGermOf (analyticAt_lgPotential (analyticAt_offQuartic a b ρ)))) :=
  exists_lgNodeMatrixFactorizationEquiv (analyticAt_offQuartic a b ρ) hρ
    (offQuartic_deriv_ne_zero ha hb hρ)

/-- **The local vacuum data cannot separate the two models.**  For any zero `ρ` of the on-line model
and any zero `ρ'` of the off-line model, the local matrix-factorization categories of the two
multiplier potentials are equivalent — although `ρ` lies on the critical line and `ρ'` does not. -/
theorem rhBlind_localMatrixFactorization_equiv {a b b₁ b₂ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hne : b₁ ≠ b₂)
    {ρ ρ' : ℂ} (hρ : onQuartic b₁ b₂ ρ = 0) (hρ' : offQuartic a b ρ' = 0) :
    Nonempty (MatrixFactorization (AnalyticGerm (ρ, (0 : ℂ)))
        (analyticGermOf (analyticAt_lgPotential (analyticAt_onQuartic b₁ b₂ ρ)))
      ≌ MatrixFactorization (AnalyticGerm (ρ', (0 : ℂ)))
        (analyticGermOf (analyticAt_lgPotential (analyticAt_offQuartic a b ρ')))) := by
  obtain ⟨e₁⟩ := onQuartic_node_category hb₁ hb₂ hne hρ
  obtain ⟨e₂⟩ := offQuartic_node_category ha hb hρ'
  exact ⟨e₁.symm.trans e₂⟩

/-- **The separation the local data misses.**  The two models are distinguished by the location of
their zeros, and by nothing in the local vacuum data. -/
theorem rhBlind_zero_separation {a b b₁ b₂ : ℝ} (ha : 0 < a)
    {ρ ρ' : ℂ} (hρ : onQuartic b₁ b₂ ρ = 0) (hρ' : offQuartic a b ρ' = 0) :
    ρ.re = 1 / 2 ∧ ρ'.re ≠ 1 / 2 :=
  ⟨onQuartic_re_eq hρ, offQuartic_re_ne ha hρ'⟩

end

end GaloisForLFunctions.RHTower
