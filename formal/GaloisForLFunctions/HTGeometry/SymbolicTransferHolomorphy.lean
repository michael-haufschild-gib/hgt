import GaloisForLFunctions.HTGeometry.SymbolicTransferBounds

/-!
# The transfer operator is entire in `s`

For a weight `w` on sequences, `(L_w g)(x) = Σ_a w(a x) g(a x)` is a bounded operator on the Hölder
space with `‖L_w‖ ≤ k (2 W₀ + W₁)` whenever `|w| ≤ W₀` and `|w(z) − w(z')| ≤ W₁ θ^j` on the
subshift (`weightedTransferOp`, `norm_le_of_apply_eq_weighted`).  The transfer operator is
`L_{e^{−sφ}}`; writing `e^{−(s₀+h)φ} − e^{−s₀φ} + h φ e^{−s₀φ} = e^{−s₀φ} ω(hφ)` with
`ω(u) = e^{−u} − 1 + u = O(u²)`, the remainder weight has both bounds of order `|h|²`, so
`s ↦ L_s` is complex differentiable with derivative `L_{−φ e^{−sφ}}` (`hasDerivAt_transferOp`).
-/

namespace GaloisForLFunctions.HTGeometry.Symbolic

open Finset

noncomputable section

variable {k : ℕ} {A : Fin k → Fin k → Prop} {ϑ : ℝ}

/-- The weighted transfer operator on functions, `(L_w g)(x) = Σ_a w(a x) g(a x)`. -/
def weightedTransferFun (w : (ℕ → Fin k) → ℂ) :
    ((ℕ → Fin k) → ℂ) →ₗ[ℂ] (ℕ → Fin k) → ℂ where
  toFun g x := ∑ a : Fin k, w (cons a x) * g (cons a x)
  map_add' g h := by funext x; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c g := by
    funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

section Weighted

variable (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθϑ : θ ≤ ϑ)

include hϑ hϑ1 hθ0 hθϑ in
/-- The pointwise bounds for a weighted sum `Σ_a w(a y) f(a y)`. -/
theorem weighted_bounds (w : (ℕ → Fin k) → ℂ) {W₀ W₁ : ℝ} (hW₀ : 0 ≤ W₀) (hW₁ : 0 ≤ W₁)
    (hw0 : ∀ z, IsAdmissible A z → ‖w z‖ ≤ W₀)
    (hw1 : ∀ z z' j, IsAdmissible A z → IsAdmissible A z' → Agree j z z' →
      ‖w z - w z'‖ ≤ W₁ * θ ^ j) (f : HolderSpace A ϑ) :
    (∀ y, ‖∑ a : Fin k, w (cons a y) * f (cons a y)‖ ≤ k * (2 * W₀ + W₁) * ‖f‖) ∧
    (∀ x y j, IsAdmissible A x → IsAdmissible A y → Agree j x y →
      ‖∑ a : Fin k, w (cons a x) * f (cons a x) - ∑ a : Fin k, w (cons a y) * f (cons a y)‖ ≤
        k * (2 * W₀ + W₁) * ‖f‖ * ϑ ^ j) := by
  have hf := norm_nonneg f
  have hsup : ∀ y, ‖∑ a : Fin k, w (cons a y) * f (cons a y)‖ ≤ k * W₀ * ‖f‖ := by
    intro y
    calc ‖∑ a : Fin k, w (cons a y) * f (cons a y)‖
        ≤ ∑ a : Fin k, ‖w (cons a y) * f (cons a y)‖ := norm_sum_le _ _
      _ ≤ ∑ _a : Fin k, W₀ * ‖f‖ := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [norm_mul]
          by_cases ha : IsAdmissible A (cons a y)
          · exact mul_le_mul (hw0 _ ha) (norm_apply_le f _) (norm_nonneg _) hW₀
          · rw [apply_of_not_adm f ha, norm_zero, mul_zero]; positivity
      _ = k * W₀ * ‖f‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨fun y => (hsup y).trans ?_, fun x y j hx hy hxy => ?_⟩
  · have : 0 ≤ k * (W₀ + W₁) * ‖f‖ := by positivity
    nlinarith
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, mul_one]
    calc _ ≤ ‖∑ a : Fin k, w (cons a x) * f (cons a x)‖ +
          ‖∑ a : Fin k, w (cons a y) * f (cons a y)‖ := norm_sub_le _ _
      _ ≤ k * W₀ * ‖f‖ + k * W₀ * ‖f‖ := add_le_add (hsup x) (hsup y)
      _ ≤ k * (2 * W₀ + W₁) * ‖f‖ := by
          have : 0 ≤ k * W₁ * ‖f‖ := by positivity
          nlinarith
  · have h0 : x 0 = y 0 := hxy 0 hj
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ a : Fin k, (w (cons a x) * f (cons a x) - w (cons a y) * f (cons a y))‖
        ≤ ∑ a : Fin k, ‖w (cons a x) * f (cons a x) - w (cons a y) * f (cons a y)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _a : Fin k, (W₀ + W₁) * ‖f‖ * ϑ ^ j := by
          refine Finset.sum_le_sum fun a _ => ?_
          by_cases ha : A a (x 0)
          · have hax : IsAdmissible A (cons a x) := (isAdmissible_cons_iff a x).mpr ⟨ha, hx⟩
            have hay : IsAdmissible A (cons a y) := (isAdmissible_cons_iff a y).mpr ⟨h0 ▸ ha, hy⟩
            have hag : Agree (j + 1) (cons a x) (cons a y) := (agree_cons_iff a x y).mpr hxy
            have hsp : w (cons a x) * f (cons a x) - w (cons a y) * f (cons a y) =
                w (cons a x) * (f (cons a x) - f (cons a y)) +
                  f (cons a y) * (w (cons a x) - w (cons a y)) := by ring
            rw [hsp]
            have hϑj : ϑ ^ (j + 1) ≤ ϑ ^ j := pow_le_pow_of_le_one hϑ.le hϑ1 (by omega)
            have hθj : θ ^ (j + 1) ≤ ϑ ^ j :=
              (pow_le_pow_left₀ hθ0 hθϑ (j + 1)).trans hϑj
            have t1 : ‖w (cons a x) * (f (cons a x) - f (cons a y))‖ ≤ W₀ * (‖f‖ * ϑ ^ j) := by
              rw [norm_mul]
              exact mul_le_mul (hw0 _ hax) ((norm_apply_sub_le hϑ f hax hay hag).trans
                (mul_le_mul_of_nonneg_left hϑj hf)) (norm_nonneg _) hW₀
            have t2 : ‖f (cons a y) * (w (cons a x) - w (cons a y))‖ ≤ ‖f‖ * (W₁ * ϑ ^ j) := by
              rw [norm_mul]
              exact mul_le_mul (norm_apply_le f _) ((hw1 _ _ _ hax hay hag).trans
                (mul_le_mul_of_nonneg_left hθj hW₁)) (norm_nonneg _) hf
            calc _ ≤ ‖w (cons a x) * (f (cons a x) - f (cons a y))‖ +
                  ‖f (cons a y) * (w (cons a x) - w (cons a y))‖ := norm_add_le _ _
              _ ≤ W₀ * (‖f‖ * ϑ ^ j) + ‖f‖ * (W₁ * ϑ ^ j) := add_le_add t1 t2
              _ = (W₀ + W₁) * ‖f‖ * ϑ ^ j := by ring
          · have hax : ¬ IsAdmissible A (cons a x) := fun h' =>
              ha ((isAdmissible_cons_iff a x).mp h').1
            have hay : ¬ IsAdmissible A (cons a y) := fun h' =>
              ha (h0 ▸ ((isAdmissible_cons_iff a y).mp h').1)
            rw [apply_of_not_adm f hax, apply_of_not_adm f hay, mul_zero, mul_zero, sub_zero,
              norm_zero]
            have := pow_nonneg hϑ.le j
            positivity
      _ = k * (W₀ + W₁) * ‖f‖ * ϑ ^ j := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ k * (2 * W₀ + W₁) * ‖f‖ * ϑ ^ j := by
          have := pow_nonneg hϑ.le j
          have : 0 ≤ k * W₀ * ‖f‖ * ϑ ^ j := by positivity
          nlinarith

include hϑ hϑ1 hθ0 hθϑ in
/-- **Operator-norm bound for a weighted transfer operator**: if `X f (y) = Σ_a w(a y) f(a y)`,
then `‖X‖ ≤ k (2 W₀ + W₁)`. -/
theorem norm_le_of_apply_eq_weighted (X : HolderSpace A ϑ →L[ℂ] HolderSpace A ϑ)
    (w : (ℕ → Fin k) → ℂ) {W₀ W₁ : ℝ} (hW₀ : 0 ≤ W₀) (hW₁ : 0 ≤ W₁)
    (hX : ∀ f y, X f y = ∑ a : Fin k, w (cons a y) * f (cons a y))
    (hw0 : ∀ z, IsAdmissible A z → ‖w z‖ ≤ W₀)
    (hw1 : ∀ z z' j, IsAdmissible A z → IsAdmissible A z' → Agree j z z' →
      ‖w z - w z'‖ ≤ W₁ * θ ^ j) :
    ‖X‖ ≤ k * (2 * W₀ + W₁) := by
  have hK : 0 ≤ (k : ℝ) * (2 * W₀ + W₁) := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun f => ?_
  obtain ⟨hs, hh⟩ := weighted_bounds hϑ hϑ1 hθ0 hθϑ w hW₀ hW₁ hw0 hw1 f
  refine norm_le_of_bounds hϑ _ (mul_nonneg hK (norm_nonneg f)) (fun y => ?_)
    (fun x y j hx hy hxy => ?_)
  · rw [hX]; exact hs y
  · rw [hX, hX]; exact hh x y j hx hy hxy

end Weighted

section WeightedOp

variable (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθϑ : θ ≤ ϑ)

/-- **The weighted transfer operator** on the Hölder space. -/
def weightedTransferOp (w : (ℕ → Fin k) → ℂ) {W₀ W₁ : ℝ} (hW₀ : 0 ≤ W₀) (hW₁ : 0 ≤ W₁)
    (hw0 : ∀ z, IsAdmissible A z → ‖w z‖ ≤ W₀)
    (hw1 : ∀ z z' j, IsAdmissible A z → IsAdmissible A z' → Agree j z z' →
      ‖w z - w z'‖ ≤ W₁ * θ ^ j) : HolderSpace A ϑ →L[ℂ] HolderSpace A ϑ :=
  ofLinear hϑ (weightedTransferFun w) (k * (2 * W₀ + W₁)) (by positivity)
    (fun f y hy => by
      show ∑ a : Fin k, w (cons a y) * f (cons a y) = 0
      refine Finset.sum_eq_zero fun a _ => ?_
      have : ¬ IsAdmissible A (cons a y) := fun h => hy ((isAdmissible_cons_iff a y).mp h).2
      rw [apply_of_not_adm f this, mul_zero])
    (fun f y => (weighted_bounds hϑ hϑ1 hθ0 hθϑ w hW₀ hW₁ hw0 hw1 f).1 y)
    (fun f x y n hx hy hxy =>
      (weighted_bounds hϑ hϑ1 hθ0 hθϑ w hW₀ hW₁ hw0 hw1 f).2 x y n hx hy hxy)

theorem weightedTransferOp_apply (w : (ℕ → Fin k) → ℂ) {W₀ W₁ : ℝ} (hW₀ : 0 ≤ W₀)
    (hW₁ : 0 ≤ W₁) (hw0) (hw1) (f : HolderSpace A ϑ) (y : ℕ → Fin k) :
    weightedTransferOp hϑ hϑ1 hθ0 hθϑ w hW₀ hW₁ hw0 hw1 f y =
      ∑ a : Fin k, w (cons a y) * f (cons a y) := by
  unfold weightedTransferOp
  rw [ofLinear_apply]
  rfl

end WeightedOp

/-! ## Two exponential remainders -/

theorem norm_one_sub_cexp_neg_le (v : ℂ) : ‖1 - Complex.exp (-v)‖ ≤ ‖v‖ * Real.exp ‖v‖ := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (-v) 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, pow_one, norm_neg] at h
  rwa [norm_sub_rev] at h

theorem norm_cexp_neg_sub_one_add_le (v : ℂ) :
    ‖Complex.exp (-v) - 1 + v‖ ≤ ‖v‖ ^ 2 * Real.exp ‖v‖ := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (-v) 2
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, pow_zero,
    Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one, norm_neg] at h
  have e : Complex.exp (-v) - (1 + -v) = Complex.exp (-v) - 1 + v := by ring
  rwa [e] at h

/-- The second-order remainder `G_h(u) = e^{−s₀u}(e^{−hu} − 1 + hu)`. -/
def expRemainder (s₀ h u : ℂ) : ℂ := Complex.exp (-(s₀ * u)) * (Complex.exp (-(h * u)) - 1 + h * u)

theorem hasDerivAt_expRemainder (s₀ h u : ℂ) :
    HasDerivAt (expRemainder s₀ h)
      (Complex.exp (-(s₀ * u)) * (-s₀) * (Complex.exp (-(h * u)) - 1 + h * u) +
        Complex.exp (-(s₀ * u)) * (h * (1 - Complex.exp (-(h * u))))) u := by
  have h1 : HasDerivAt (fun u => Complex.exp (-(s₀ * u))) (Complex.exp (-(s₀ * u)) * (-s₀)) u := by
    have := ((hasDerivAt_id u).const_mul s₀).neg.cexp
    simpa using this
  have h2 : HasDerivAt (fun u => Complex.exp (-(h * u)) - 1 + h * u)
      (h * (1 - Complex.exp (-(h * u)))) u := by
    have e1 : HasDerivAt (fun u => Complex.exp (-(h * u))) (Complex.exp (-(h * u)) * (-h)) u := by
      have := ((hasDerivAt_id u).const_mul h).neg.cexp
      simpa using this
    have := ((e1.sub_const 1).add ((hasDerivAt_id u).const_mul h))
    exact this.congr_deriv (by ring)
  exact h1.mul h2

/-- **The remainder is `O(|h|²)` and `O(|h|²)`-Lipschitz** on `|u| ≤ R₀`, for `|h| ≤ 1`. -/
theorem norm_expRemainder_le (s₀ : ℂ) {h u : ℂ} {R₀ : ℝ} (hh : ‖h‖ ≤ 1) (hu : ‖u‖ ≤ R₀) :
    ‖expRemainder s₀ h u‖ ≤ Real.exp (‖s₀‖ * R₀) * (R₀ ^ 2 * Real.exp R₀) * ‖h‖ ^ 2 := by
  have hR₀ : 0 ≤ R₀ := (norm_nonneg u).trans hu
  have hhu : ‖h * u‖ ≤ R₀ := by
    rw [norm_mul]; calc ‖h‖ * ‖u‖ ≤ 1 * R₀ := mul_le_mul hh hu (norm_nonneg _) zero_le_one
      _ = R₀ := one_mul _
  rw [expRemainder, norm_mul]
  have e1 : ‖Complex.exp (-(s₀ * u))‖ ≤ Real.exp (‖s₀‖ * R₀) := by
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_neg, norm_mul]; exact mul_le_mul_of_nonneg_left hu (norm_nonneg _)
  have e2 : ‖Complex.exp (-(h * u)) - 1 + h * u‖ ≤ (R₀ ^ 2 * Real.exp R₀) * ‖h‖ ^ 2 := by
    refine (norm_cexp_neg_sub_one_add_le (h * u)).trans ?_
    rw [norm_mul, mul_pow]
    have : Real.exp (‖h‖ * ‖u‖) ≤ Real.exp R₀ := Real.exp_le_exp.mpr (by rw [← norm_mul]; exact hhu)
    calc ‖h‖ ^ 2 * ‖u‖ ^ 2 * Real.exp (‖h‖ * ‖u‖) ≤ ‖h‖ ^ 2 * R₀ ^ 2 * Real.exp R₀ := by
          gcongr
      _ = R₀ ^ 2 * Real.exp R₀ * ‖h‖ ^ 2 := by ring
  calc ‖Complex.exp (-(s₀ * u))‖ * ‖Complex.exp (-(h * u)) - 1 + h * u‖
      ≤ Real.exp (‖s₀‖ * R₀) * ((R₀ ^ 2 * Real.exp R₀) * ‖h‖ ^ 2) :=
        mul_le_mul e1 e2 (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

/-- The Lipschitz constant of the remainder on `|u| ≤ R₀`. -/
def remainderLipConst (s₀ : ℂ) (R₀ : ℝ) : ℝ :=
  Real.exp (‖s₀‖ * R₀) * (‖s₀‖ * (R₀ ^ 2 * Real.exp R₀) + R₀ * Real.exp R₀)

theorem norm_expRemainder_sub_le (s₀ : ℂ) {h : ℂ} {R₀ : ℝ} (hh : ‖h‖ ≤ 1) {a b : ℂ}
    (ha : ‖a‖ ≤ R₀) (hb : ‖b‖ ≤ R₀) :
    ‖expRemainder s₀ h a - expRemainder s₀ h b‖ ≤ remainderLipConst s₀ R₀ * ‖h‖ ^ 2 * ‖a - b‖ := by
  have hR₀ : 0 ≤ R₀ := (norm_nonneg a).trans ha
  have hderiv : ∀ u ∈ Metric.closedBall (0 : ℂ) R₀,
      ‖deriv (expRemainder s₀ h) u‖ ≤ remainderLipConst s₀ R₀ * ‖h‖ ^ 2 := by
    intro u hu
    have hu' : ‖u‖ ≤ R₀ := mem_closedBall_zero_iff.mp hu
    have hhu : ‖h * u‖ ≤ R₀ := by
      rw [norm_mul]; calc ‖h‖ * ‖u‖ ≤ 1 * R₀ := mul_le_mul hh hu' (norm_nonneg _) zero_le_one
        _ = R₀ := one_mul _
    rw [(hasDerivAt_expRemainder s₀ h u).deriv]
    have e1 : ‖Complex.exp (-(s₀ * u))‖ ≤ Real.exp (‖s₀‖ * R₀) := by
      refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_neg, norm_mul]; exact mul_le_mul_of_nonneg_left hu' (norm_nonneg _)
    have e2 : ‖Complex.exp (-(h * u)) - 1 + h * u‖ ≤ (R₀ ^ 2 * Real.exp R₀) * ‖h‖ ^ 2 := by
      refine (norm_cexp_neg_sub_one_add_le (h * u)).trans ?_
      rw [norm_mul, mul_pow]
      have : Real.exp (‖h‖ * ‖u‖) ≤ Real.exp R₀ :=
        Real.exp_le_exp.mpr (by rw [← norm_mul]; exact hhu)
      calc ‖h‖ ^ 2 * ‖u‖ ^ 2 * Real.exp (‖h‖ * ‖u‖) ≤ ‖h‖ ^ 2 * R₀ ^ 2 * Real.exp R₀ := by
            gcongr
        _ = R₀ ^ 2 * Real.exp R₀ * ‖h‖ ^ 2 := by ring
    have e3 : ‖h * (1 - Complex.exp (-(h * u)))‖ ≤ R₀ * Real.exp R₀ * ‖h‖ ^ 2 := by
      rw [norm_mul]
      have h1 := norm_one_sub_cexp_neg_le (h * u)
      have h2 : ‖h * u‖ ≤ ‖h‖ * R₀ := by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left hu' (norm_nonneg _)
      have h3 : Real.exp ‖h * u‖ ≤ Real.exp R₀ := Real.exp_le_exp.mpr hhu
      calc ‖h‖ * ‖1 - Complex.exp (-(h * u))‖ ≤ ‖h‖ * (‖h‖ * R₀ * Real.exp R₀) := by
            refine mul_le_mul_of_nonneg_left (h1.trans ?_) (norm_nonneg _)
            exact mul_le_mul h2 h3 (Real.exp_pos _).le (by positivity)
        _ = R₀ * Real.exp R₀ * ‖h‖ ^ 2 := by ring
    calc ‖Complex.exp (-(s₀ * u)) * -s₀ * (Complex.exp (-(h * u)) - 1 + h * u) +
          Complex.exp (-(s₀ * u)) * (h * (1 - Complex.exp (-(h * u))))‖
        ≤ ‖Complex.exp (-(s₀ * u)) * -s₀ * (Complex.exp (-(h * u)) - 1 + h * u)‖ +
          ‖Complex.exp (-(s₀ * u)) * (h * (1 - Complex.exp (-(h * u))))‖ := norm_add_le _ _
      _ ≤ Real.exp (‖s₀‖ * R₀) * ‖s₀‖ * ((R₀ ^ 2 * Real.exp R₀) * ‖h‖ ^ 2) +
          Real.exp (‖s₀‖ * R₀) * (R₀ * Real.exp R₀ * ‖h‖ ^ 2) := by
          rw [norm_mul, norm_mul, norm_neg, norm_mul]
          gcongr
      _ = remainderLipConst s₀ R₀ * ‖h‖ ^ 2 := by unfold remainderLipConst; ring
  have := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun u _ => (hasDerivAt_expRemainder s₀ h u).differentiableAt) hderiv (convex_closedBall 0 R₀)
    (mem_closedBall_zero_iff.mpr hb) (mem_closedBall_zero_iff.mpr ha)
  exact this

/-! ## The derivative in `s` -/

/-- The derivative weight `−φ e^{−sφ}`. -/
def derivWeight (φ : (ℕ → Fin k) → ℝ) (s : ℂ) : (ℕ → Fin k) → ℂ :=
  fun z => -((φ z : ℂ) * Complex.exp (-(s * φ z)))

section Holomorphy

variable (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ}
  (hφ : IsHolderPotential A φ R₀ C θ) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθϑ : θ ≤ ϑ) (hθ1 : θ < 1)
  (hR₀ : 0 ≤ R₀)

include hφ in
theorem norm_derivWeight_le (s : ℂ) {z : ℕ → Fin k} (hz : IsAdmissible A z) :
    ‖derivWeight φ s z‖ ≤ R₀ * Real.exp (|s.re| * R₀) := by
  rw [derivWeight, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_cexp_neg_mul_ofReal]
  have hb := hφ.bound z hz
  have he : Real.exp (-(s.re * φ z)) ≤ Real.exp (|s.re| * R₀) := by
    refine Real.exp_le_exp.mpr ?_
    have : -(s.re * φ z) ≤ |s.re| * |φ z| := by rw [← abs_mul]; exact neg_le_abs _
    exact this.trans (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
  exact mul_le_mul hb he (Real.exp_pos _).le ((abs_nonneg _).trans hb)

include hφ hθ0 hθ1 hC in
theorem norm_derivWeight_sub_le (s : ℂ) {z z' : ℕ → Fin k} {j : ℕ} (hz : IsAdmissible A z)
    (hz' : IsAdmissible A z') (hzz : Agree j z z') :
    ‖derivWeight φ s z - derivWeight φ s z'‖ ≤
      (C * Real.exp (|s.re| * R₀) * (1 + R₀ * (‖s‖ * Real.exp (‖s‖ * C)))) * θ ^ j := by
  have hb := hφ.bound z' hz'
  have hR₀ : 0 ≤ R₀ := (abs_nonneg _).trans hb
  have hhol := hφ.holder z z' j hz hz' hzz
  have hθj1 : θ ^ j ≤ 1 := pow_le_one₀ hθ0 hθ1.le
  have hsplit : derivWeight φ s z - derivWeight φ s z' =
      -(((φ z : ℂ) - φ z') * Complex.exp (-(s * φ z))) +
        (φ z' : ℂ) * (Complex.exp (-(s * φ z')) - Complex.exp (-(s * φ z))) := by
    simp only [derivWeight]; ring
  rw [hsplit]
  have e1 : ‖((φ z : ℂ) - φ z') * Complex.exp (-(s * φ z))‖ ≤
      C * θ ^ j * Real.exp (|s.re| * R₀) := by
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      norm_cexp_neg_mul_ofReal]
    refine mul_le_mul hhol (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
      (mul_nonneg hC (pow_nonneg hθ0 j))
    have : -(s.re * φ z) ≤ |s.re| * |φ z| := by rw [← abs_mul]; exact neg_le_abs _
    exact this.trans (mul_le_mul_of_nonneg_left (hφ.bound z hz) (abs_nonneg _))
  have e2 : ‖(φ z' : ℂ) * (Complex.exp (-(s * φ z')) - Complex.exp (-(s * φ z)))‖ ≤
      R₀ * (Real.exp (|s.re| * R₀) * (‖s‖ * (C * θ ^ j) * Real.exp (‖s‖ * C))) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul hb (norm_cexp_sub_le_of_bounds s hb ?_ ?_) (norm_nonneg _) hR₀
    · rw [abs_sub_comm]; exact hhol
    · exact mul_le_of_le_one_right hC hθj1
  calc _ ≤ ‖((φ z : ℂ) - φ z') * Complex.exp (-(s * φ z))‖ +
        ‖(φ z' : ℂ) * (Complex.exp (-(s * φ z')) - Complex.exp (-(s * φ z)))‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_neg]
    _ ≤ C * θ ^ j * Real.exp (|s.re| * R₀) +
        R₀ * (Real.exp (|s.re| * R₀) * (‖s‖ * (C * θ ^ j) * Real.exp (‖s‖ * C))) := add_le_add e1 e2
    _ = _ := by ring

/-- **The derivative of the transfer operator in `s`**, `f ↦ Σ_a −φ(a·) e^{−sφ(a·)} f(a·)`. -/
def transferDerivOp (s : ℂ) : HolderSpace A ϑ →L[ℂ] HolderSpace A ϑ :=
  weightedTransferOp hϑ hϑ1 hθ0 hθϑ (derivWeight φ s)
    (mul_nonneg hR₀ (Real.exp_pos _).le) (by positivity)
    (fun z hz => norm_derivWeight_le hφ s hz)
    (fun z z' j hz hz' hzz => norm_derivWeight_sub_le hφ hC hθ0 hθ1 s hz hz' hzz)

include hR₀ in
/-- **The transfer operator is complex differentiable in `s`.** -/
theorem hasDerivAt_transferOp (s₀ : ℂ) :
    HasDerivAt (fun s => transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s)
      (transferDerivOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 hR₀ s₀) s₀ := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  set W₀' := Real.exp (‖s₀‖ * R₀) * (R₀ ^ 2 * Real.exp R₀)
  set L := remainderLipConst s₀ R₀
  have hL : 0 ≤ L := by unfold L remainderLipConst; positivity
  set c := (k : ℝ) * (2 * W₀' + L * C)
  have hc : 0 ≤ c := by positivity
  have hrad : 0 < min 1 (ε / (c + 1)) := lt_min one_pos (by positivity)
  filter_upwards [Metric.ball_mem_nhds s₀ hrad] with s hs
  set h := s - s₀
  have hh : ‖h‖ < min 1 (ε / (c + 1)) := by rw [← dist_eq_norm]; exact hs
  have hh1 : ‖h‖ ≤ 1 := (lt_of_lt_of_le hh (min_le_left _ _)).le
  have hhε : ‖h‖ ≤ ε / (c + 1) := (lt_of_lt_of_le hh (min_le_right _ _)).le
  set X := transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s - transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s₀ -
    h • transferDerivOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 hR₀ s₀
  have hX : ∀ f y, X f y = ∑ a : Fin k, expRemainder s₀ h (φ (cons a y)) * f (cons a y) := by
    intro f y
    simp only [X, _root_.sub_apply, _root_.smul_apply, sub_apply, smul_apply,
      transferOp_apply, transferFun_apply, transferDerivOp, weightedTransferOp_apply,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hs' : s = s₀ + h := by simp [h]
    simp only [expRemainder, derivWeight]
    rw [hs']
    have : Complex.exp (-((s₀ + h) * (φ (cons a y) : ℂ))) =
        Complex.exp (-(s₀ * φ (cons a y))) * Complex.exp (-(h * φ (cons a y))) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [this]
    ring
  have hw0 : ∀ z, IsAdmissible A z → ‖expRemainder s₀ h (φ z)‖ ≤ W₀' * ‖h‖ ^ 2 := by
    intro z hz
    refine norm_expRemainder_le s₀ hh1 ?_
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hφ.bound z hz
  have hw1 : ∀ z z' j, IsAdmissible A z → IsAdmissible A z' → Agree j z z' →
      ‖expRemainder s₀ h (φ z) - expRemainder s₀ h (φ z')‖ ≤ (L * ‖h‖ ^ 2 * C) * θ ^ j := by
    intro z z' j hz hz' hzz
    have := norm_expRemainder_sub_le s₀ hh1 (R₀ := R₀) (a := (φ z : ℂ)) (b := (φ z' : ℂ))
      (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hφ.bound z hz)
      (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hφ.bound z' hz')
    refine this.trans ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, mul_assoc (L * ‖h‖ ^ 2)]
    exact mul_le_mul_of_nonneg_left (hφ.holder z z' j hz hz' hzz) (by positivity)
  have hnorm := norm_le_of_apply_eq_weighted hϑ hϑ1 hθ0 hθϑ X (fun z => expRemainder s₀ h (φ z))
    (by positivity) (by positivity) hX hw0 hw1
  calc ‖X‖ ≤ k * (2 * (W₀' * ‖h‖ ^ 2) + L * ‖h‖ ^ 2 * C) := hnorm
    _ = c * ‖h‖ * ‖h‖ := by ring
    _ ≤ ε * ‖h‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        calc c * ‖h‖ ≤ c * (ε / (c + 1)) := mul_le_mul_of_nonneg_left hhε hc
          _ ≤ ε := by
              rw [mul_div_assoc', div_le_iff₀ (by linarith)]
              nlinarith

include hR₀ in
/-- **`s ↦ L_s` is entire.** -/
theorem differentiable_transferOp :
    Differentiable ℂ fun s => transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s :=
  fun s₀ => (hasDerivAt_transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 hR₀ s₀).differentiableAt

end Holomorphy

end

end GaloisForLFunctions.HTGeometry.Symbolic
