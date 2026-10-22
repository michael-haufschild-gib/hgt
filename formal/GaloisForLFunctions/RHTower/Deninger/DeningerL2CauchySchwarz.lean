import GaloisForLFunctions.RHTower.Deninger.DeningerKummerL2Bilinear

/-!
# Cauchy--Schwarz for the `L²` form on the Kummer space

Expanding `⟨x + t y, x + t y⟩ ≥ 0` gives a quadratic in `t` that is nonnegative at every *rational*
`t`; being continuous it is then nonnegative at every real `t`, and the discriminant condition is
the Cauchy--Schwarz inequality.

* `deningerSpaceL2_quadratic_nonneg` : the quadratic is nonnegative at every real scalar.
* `deningerSpaceL2_cauchySchwarz` : `⟨x, y⟩² ≤ ⟨x, x⟩ · ⟨y, y⟩`.
-/

namespace RHTower

open NumberField

section CauchySchwarz

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

/-- The expansion of the form on `x + q y`. -/
theorem deningerSpaceL2Inner_add_qsmul (q : ℚ) (x y : deningerKummerSpace F) :
    deningerSpaceL2Inner (x + q • y) (x + q • y)
      = deningerSpaceL2Inner y y * (q : ℝ) * (q : ℝ)
        + 2 * deningerSpaceL2Inner x y * (q : ℝ) + deningerSpaceL2Inner x x := by
  have hqq : deningerSpaceL2Inner (q • y) (q • y)
      = (q : ℝ) * ((q : ℝ) * deningerSpaceL2Inner y y) := by
    rw [deningerSpaceL2Inner_qsmul_left, deningerSpaceL2Inner_comm y (q • y),
      deningerSpaceL2Inner_qsmul_left, deningerSpaceL2Inner_comm y y]
  rw [deningerSpaceL2Inner_add_left, deningerSpaceL2Inner_add_right,
    deningerSpaceL2Inner_add_right, deningerSpaceL2Inner_qsmul_left,
    deningerSpaceL2Inner_comm x (q • y), deningerSpaceL2Inner_qsmul_left,
    deningerSpaceL2Inner_comm y x, hqq]
  ring

/-- **The quadratic is nonnegative at every real scalar.** -/
theorem deningerSpaceL2_quadratic_nonneg (x y : deningerKummerSpace F) (t : ℝ) :
    0 ≤ deningerSpaceL2Inner y y * (t * t)
      + 2 * deningerSpaceL2Inner x y * t + deningerSpaceL2Inner x x := by
  set A : ℝ := deningerSpaceL2Inner x x with hA
  set B : ℝ := deningerSpaceL2Inner x y with hB
  set C : ℝ := deningerSpaceL2Inner y y with hC
  have hrat : ∀ q : ℚ, 0 ≤ C * ((q : ℝ) * (q : ℝ)) + 2 * B * (q : ℝ) + A := by
    intro q
    have hexp := deningerSpaceL2Inner_add_qsmul q x y
    have hnn := deningerSpaceL2Inner_self_nonneg (x + q • y)
    rw [hexp] at hnn
    linarith [hnn]
  have hcont : Continuous fun t : ℝ => C * (t * t) + 2 * B * t + A := by
    fun_prop
  have hclosed : IsClosed {t : ℝ | 0 ≤ C * (t * t) + 2 * B * t + A} :=
    isClosed_le continuous_const hcont
  have hsub : Set.range ((↑) : ℚ → ℝ) ⊆ {t : ℝ | 0 ≤ C * (t * t) + 2 * B * t + A} := by
    rintro _ ⟨q, rfl⟩
    exact hrat q
  have huniv : (Set.univ : Set ℝ) ⊆ {t : ℝ | 0 ≤ C * (t * t) + 2 * B * t + A} := by
    rw [← Rat.denseRange_cast.closure_range]
    exact hclosed.closure_subset_iff.mpr hsub
  exact huniv (Set.mem_univ t)

/-- **Cauchy--Schwarz for the `L²` form.** -/
theorem deningerSpaceL2_cauchySchwarz (x y : deningerKummerSpace F) :
    deningerSpaceL2Inner x y * deningerSpaceL2Inner x y
      ≤ deningerSpaceL2Inner x x * deningerSpaceL2Inner y y := by
  have hdisc := discrim_le_zero (a := deningerSpaceL2Inner y y)
    (b := 2 * deningerSpaceL2Inner x y) (c := deningerSpaceL2Inner x x)
    (deningerSpaceL2_quadratic_nonneg x y)
  rw [discrim] at hdisc
  nlinarith [hdisc]

end CauchySchwarz

end RHTower
