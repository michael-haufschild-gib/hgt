import GaloisForLFunctions.RHTower.DeningerBarSquareZero

/-!
# The two-term Milnor algebra, reflection, and the completed bar complex

The two-term algebra `B_H = ℂ·1 ⊕ 𝒦_H⁰` has the square-zero product, whose seminorms are
submultiplicative for `q_k(λ,a) = |λ| + p_k(a)`.  Its bar source is complete with dense finitely
supported vectors, its differential squares to zero, and componentwise reflection of the letters
is an isometric chain map which reverses the arithmetic character.

Because no nonunit letter has character zero, the length-one part of the sector of total character
zero is exactly the scalar line.

* `deningerTwoTermMul`, `deningerTwoTermSeminorm_mul_le` : the algebra and its submultiplicativity.
* `deningerBarDiff_comp_self` : **`b² = 0` on the source.**
* `deningerBarReflect` : reflection, with its isometry and chain property.
* `deningerBarChar_one_eq_zero_iff` : the length-one zero sector is the scalar line.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-! ## The two-term Milnor algebra -/

/-- **The completed two-term Milnor algebra** `B_H = ℂ·1 ⊕ 𝒦_H⁰`. -/
abbrev DeningerTwoTerm : Type :=
  ℂ × (deningerHeightKotheZero : Submodule ℂ DeningerHeightKothe)

/-- The square-zero product `(λ,a)(μ,b) = (λμ, λb + μa)`. -/
def deningerTwoTermMul (x y : DeningerTwoTerm) : DeningerTwoTerm :=
  (x.1 * y.1, x.1 • y.2 + y.1 • x.2)

/-- The seminorm `q_k(λ,a) = |λ| + p_k(a)`. -/
def deningerTwoTermSeminorm (k : ℕ) (x : DeningerTwoTerm) : ℝ :=
  ‖x.1‖ + deningerHeightSeminorm k ((x.2 : DeningerHeightKothe))

theorem deningerTwoTermSeminorm_nonneg (k : ℕ) (x : DeningerTwoTerm) :
    0 ≤ deningerTwoTermSeminorm k x :=
  add_nonneg (norm_nonneg _) (apply_nonneg _ _)

/-- **The seminorms of the two-term algebra are submultiplicative.** -/
theorem deningerTwoTermSeminorm_mul_le (k : ℕ) (x y : DeningerTwoTerm) :
    deningerTwoTermSeminorm k (deningerTwoTermMul x y)
      ≤ deningerTwoTermSeminorm k x * deningerTwoTermSeminorm k y := by
  have hx : (0 : ℝ) ≤ deningerHeightSeminorm k ((x.2 : DeningerHeightKothe)) :=
    apply_nonneg _ _
  have hy : (0 : ℝ) ≤ deningerHeightSeminorm k ((y.2 : DeningerHeightKothe)) :=
    apply_nonneg _ _
  have hstep : deningerHeightSeminorm k
      (((x.1 • y.2 + y.1 • x.2 : deningerHeightKotheZero) : DeningerHeightKothe))
      ≤ ‖x.1‖ * deningerHeightSeminorm k ((y.2 : DeningerHeightKothe))
        + ‖y.1‖ * deningerHeightSeminorm k ((x.2 : DeningerHeightKothe)) := by
    have hcoe : ((x.1 • y.2 + y.1 • x.2 : deningerHeightKotheZero) : DeningerHeightKothe)
        = x.1 • (y.2 : DeningerHeightKothe) + y.1 • (x.2 : DeningerHeightKothe) := rfl
    rw [hcoe]
    refine le_trans (map_add_le_add _ _ _) ?_
    rw [map_smul_eq_mul, map_smul_eq_mul]
  rw [deningerTwoTermSeminorm, deningerTwoTermMul, deningerTwoTermSeminorm,
    deningerTwoTermSeminorm, norm_mul]
  nlinarith [norm_nonneg x.1, norm_nonneg y.1]

/-! ## The differential squares to zero on the source -/

/-- **`b² = 0` on the entire word-height bar source.** -/
theorem deningerBarDiff_comp_self (c : DeningerBarKothe) :
    deningerBarDiff (deningerBarDiff c) = 0 := by
  ext w
  show deningerBarDiffCoe (deningerBarDiffCoe (c : DeningerBarWord → ℂ)) w = _
  rw [deningerBarDiffCoe_comp_self]
  rfl

/-! ## Completeness and density of the bar source -/

/-- **The bar source is sequentially complete.** -/
theorem deningerBarKothe_exists_limit (a : ℕ → DeningerBarKothe)
    (h : DeningerKotheCauchy deningerBarKotheData a) :
    ∃ L : DeningerBarKothe, DeningerKotheTendsto deningerBarKotheData a L :=
  deningerKothe_exists_limit a h

/-- **The finitely supported words are dense in the bar source.** -/
theorem deningerBarKothe_exists_finite_approx (a : DeningerBarKothe) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset DeningerBarWord,
      deningerBarSeminorm k
        (a - ∑ w ∈ S, (a : DeningerBarWord → ℂ) w •
          (deningerKotheDelta deningerBarKotheData w : DeningerBarKothe)) < ε := by
  classical
  obtain ⟨S, hS⟩ := deningerKothe_exists_finite_approx a k hε
  exact ⟨S, hS⟩

/-- **The bar source is nuclear.** -/
theorem deningerBarKothe_isNuclearSpace :
    DeningerIsNuclearSpace (deningerKotheSeminorm (𝕜 := ℂ) deningerBarKotheData) := by
  classical
  exact deningerKothe_isNuclearSpace _ deningerBarKotheData_isNuclear

/-! ## The length-one zero sector -/

/-- **No nonunit letter has character zero**, so the length-one part of the balanced sector is
exactly the scalar line. -/
theorem deningerBarChar_one_eq_zero_iff (f : Fin 1 → DeningerLattice) :
    deningerBarChar (⟨0, f⟩ : DeningerBarWord) = 0 ↔ f 0 = 0 := by
  show (∑ i, f i) = 0 ↔ f 0 = 0
  rw [Fin.sum_univ_one]

/-! ## Reflection -/

/-- Componentwise reflection of the letters of a word. -/
def deningerBarReflectWord (w : DeningerBarWord) : DeningerBarWord :=
  ⟨w.1, fun j => -(w.2 j)⟩

@[simp]
theorem deningerBarReflectWord_involutive (w : DeningerBarWord) :
    deningerBarReflectWord (deningerBarReflectWord w) = w := by
  obtain ⟨r, f⟩ := w
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext j
  show - -(f j) = f j
  rw [neg_neg]

theorem deningerBarReflectWord_height (w : DeningerBarWord) :
    deningerBarHeight (deningerBarReflectWord w) = deningerBarHeight w := by
  obtain ⟨r, f⟩ := w
  show (∏ j, deningerHeight (-(f j))) = ∏ j, deningerHeight (f j)
  exact Finset.prod_congr rfl fun j _ => deningerHeight_neg (f j)

@[simp]
theorem deningerBarReflectWord_length (w : DeningerBarWord) :
    deningerBarLength (deningerBarReflectWord w) = deningerBarLength w := rfl

theorem deningerBarReflectWord_char (w : DeningerBarWord) :
    deningerBarChar (deningerBarReflectWord w) = -deningerBarChar w := by
  obtain ⟨r, f⟩ := w
  show (∑ j, -(f j)) = -∑ j, f j
  rw [Finset.sum_neg_distrib]

theorem deningerBarReflectWord_injective :
    Function.Injective deningerBarReflectWord := by
  intro w w' h
  have := congrArg deningerBarReflectWord h
  rwa [deningerBarReflectWord_involutive, deningerBarReflectWord_involutive] at this

private theorem deningerBarReflect_mem (c : DeningerBarKothe) :
    (fun w => (c : DeningerBarWord → ℂ) (deningerBarReflectWord w)) ∈ DeningerBarKothe := by
  intro k
  have hcomp := (c.2 k).comp_injective deningerBarReflectWord_injective
  refine hcomp.congr fun w => ?_
  simp only [Function.comp_apply, deningerBarKotheData_w, deningerBarReflectWord_height,
    deningerBarReflectWord_length]

/-- **Reflection** of the bar source. -/
def deningerBarReflect : DeningerBarKothe →ₗ[ℂ] DeningerBarKothe where
  toFun c := ⟨fun w => (c : DeningerBarWord → ℂ) (deningerBarReflectWord w),
    deningerBarReflect_mem c⟩
  map_add' a b := by
    ext w
    show ((a + b : DeningerBarKothe) : DeningerBarWord → ℂ) (deningerBarReflectWord w) = _
    rw [Submodule.coe_add, Pi.add_apply]
    rfl
  map_smul' t a := by
    ext w
    show ((t • a : DeningerBarKothe) : DeningerBarWord → ℂ) (deningerBarReflectWord w) = _
    rw [Submodule.coe_smul, Pi.smul_apply]
    rfl

@[simp]
theorem deningerBarReflect_coe (c : DeningerBarKothe) (w : DeningerBarWord) :
    ((deningerBarReflect c : DeningerBarKothe) : DeningerBarWord → ℂ) w
      = (c : DeningerBarWord → ℂ) (deningerBarReflectWord w) := rfl

/-- **Reflection is a seminorm isometry.** -/
theorem deningerBarSeminorm_reflect (k : ℕ) (c : DeningerBarKothe) :
    deningerBarSeminorm k (deningerBarReflect c) = deningerBarSeminorm k c := by
  rw [deningerBarSeminorm_apply, deningerBarSeminorm_apply]
  have hbij : Function.Bijective deningerBarReflectWord := by
    refine ⟨deningerBarReflectWord_injective, fun w => ⟨deningerBarReflectWord w, ?_⟩⟩
    exact deningerBarReflectWord_involutive w
  rw [← (Equiv.ofBijective _ hbij).tsum_eq
    (fun w => deningerBarKotheData.w k w * ‖(c : DeningerBarWord → ℂ) w‖)]
  refine tsum_congr fun w => ?_
  show deningerBarKotheData.w k w * ‖(c : DeningerBarWord → ℂ) (deningerBarReflectWord w)‖
      = deningerBarKotheData.w k (deningerBarReflectWord w) *
        ‖(c : DeningerBarWord → ℂ) (deningerBarReflectWord w)‖
  rw [deningerBarKotheData_w, deningerBarKotheData_w, deningerBarReflectWord_height,
    deningerBarReflectWord_length]

/-- Reflection commutes with unit insertion. -/
theorem deningerBarReflectWord_insert {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerLattice) :
    deningerBarReflectWord (deningerInsertUnitWord t f)
      = deningerInsertUnitWord t (fun j => -(f j)) := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i
  refine Fin.succAboveCases (α := fun i =>
      -(deningerInsertUnit t f i) = deningerInsertUnit t (fun j => -(f j)) i) t ?_ ?_ i
  · rw [deningerInsertUnit_same, deningerInsertUnit_same, neg_zero]
  · intro k
    rw [deningerInsertUnit_succAbove, deningerInsertUnit_succAbove]

/-- **Reflection is a chain map for the bar differential.** -/
theorem deningerBarReflect_diff (c : DeningerBarWord → ℂ) :
    deningerBarDiffCoe (fun w => c (deningerBarReflectWord w))
      = fun w => deningerBarDiffCoe c (deningerBarReflectWord w) := by
  funext w
  obtain ⟨s, f⟩ := w
  have hfibre : ∀ j : Fin (s + 1),
      deningerBarFibreSum (fun w => c (deningerBarReflectWord w)) f j
        = deningerBarFibreSum c (fun j => -(f j)) j := by
    intro j
    have hz : f j = 0 ↔ (fun j => -(f j)) j = 0 := by
      constructor
      · intro h; show -(f j) = 0; rw [h, neg_zero]
      · intro h; have h' : -(f j) = 0 := h; rw [← neg_neg (f j), h', neg_zero]
    rw [deningerBarFibreSum, deningerBarFibreSum]
    by_cases h : f j = 0
    · rw [if_pos h, if_pos (hz.mp h)]
      show c (deningerBarReflectWord (deningerInsertUnitWord j.castSucc f)) = _
      rw [deningerBarReflectWord_insert]
    · rw [if_neg h, if_neg (fun hc => h (hz.mpr hc))]
      show c (deningerBarReflectWord (deningerInsertUnitWord j.castSucc f))
          + c (deningerBarReflectWord (deningerInsertUnitWord j.succ f)) = _
      rw [deningerBarReflectWord_insert, deningerBarReflectWord_insert]
  show (∑ j : Fin (s + 1), (-1 : ℂ) ^ (j : ℕ) *
      deningerBarFibreSum (fun w => c (deningerBarReflectWord w)) f j) = _
  show _ = ∑ j : Fin (s + 1), (-1 : ℂ) ^ (j : ℕ) *
      deningerBarFibreSum c (fun j => -(f j)) j
  exact Finset.sum_congr rfl fun j _ => by rw [hfibre j]

/-- **Reflection is a chain map on the source.** -/
theorem deningerBarReflect_diff_op (c : DeningerBarKothe) :
    deningerBarDiff (deningerBarReflect c) = deningerBarReflect (deningerBarDiff c) := by
  ext w
  show deningerBarDiffCoe
      (fun w => (c : DeningerBarWord → ℂ) (deningerBarReflectWord w)) w = _
  rw [deningerBarReflect_diff]
  rfl

end

end RHTower
