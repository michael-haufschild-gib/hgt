import GaloisForLFunctions.ArithmeticPositiveDuality.UniformRealZeroDivisionBounds

/-!
# Theta sources for finite monomial donor surgery

One normalized sine resolvent supplies the last denominator factor.
Each further step applies `I-(γ²+1/4)Sγ`, multiplying the transform by
`(-z²-1/4)/(γ²-z²)`. Distinct actual donors remain zeros until divided.
-/

noncomputable section
set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology RHTower

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- The source with transform `XiC(z)(-z²-1/4)^m / ∏(γᵢ²-z²)`. -/
def finiteDonorThetaSource : (m : ℕ) → (Fin (m + 1) → ℝ) → ℝ → ℝ
  | 0, γ => realZeroResolvent (γ 0) thetaCuspFullSource
  | m + 1, γ => fun x => finiteDonorThetaSource m (Fin.tail γ) x -
      (γ 0 ^ 2 + 1 / 4) * realZeroResolvent (γ 0)
        (finiteDonorThetaSource m (Fin.tail γ)) x

theorem finiteDonorThetaSource_even (m : ℕ) (γ : Fin (m + 1) → ℝ) (x : ℝ) :
    finiteDonorThetaSource m γ (-x) = finiteDonorThetaSource m γ x := by
  induction m with
  | zero => exact realZeroResolvent_even _ _ _
  | succ m ih =>
    simp only [finiteDonorThetaSource, ih, realZeroResolvent_even]

theorem expMomentSource_finiteDonorThetaSource (m : ℕ) (γ : Fin (m + 1) → ℝ) :
    ExpMomentSource (fun x => (finiteDonorThetaSource m γ x : ℂ)) := by
  induction m with
  | zero => exact expMomentSource_realZeroResolvent _ expMomentSource_thetaSourceC
  | succ m ih =>
    have he : (fun x => (finiteDonorThetaSource (m + 1) γ x : ℂ)) =
        fun x => (finiteDonorThetaSource m (Fin.tail γ) x : ℂ) +
          (-((γ 0 ^ 2 + 1 / 4 : ℝ) : ℂ)) *
            (realZeroResolvent (γ 0) (finiteDonorThetaSource m (Fin.tail γ)) x : ℂ) := by
      funext x
      simp only [finiteDonorThetaSource, Complex.ofReal_sub, Complex.ofReal_mul]
      ring
    rw [he]
    exact (ih (Fin.tail γ)).add
      ((expMomentSource_realZeroResolvent _ (ih (Fin.tail γ))).const_mul _)

private theorem sourceTransform_finiteDonorThetaSource_succ (m : ℕ)
    (γ : Fin (m + 2) → ℝ) (z : ℂ) :
    sourceTransform (fun x => (finiteDonorThetaSource (m + 1) γ x : ℂ)) z =
      sourceTransform (fun x => (finiteDonorThetaSource m (Fin.tail γ) x : ℂ)) z -
      ((γ 0 ^ 2 + 1 / 4 : ℝ) : ℂ) * sourceTransform
        (fun x => (realZeroResolvent (γ 0) (finiteDonorThetaSource m (Fin.tail γ)) x : ℂ)) z := by
  have he : (fun x => (finiteDonorThetaSource (m + 1) γ x : ℂ)) =
      fun x => (finiteDonorThetaSource m (Fin.tail γ) x : ℂ) +
        (-((γ 0 ^ 2 + 1 / 4 : ℝ) : ℂ)) *
          (realZeroResolvent (γ 0) (finiteDonorThetaSource m (Fin.tail γ)) x : ℂ) := by
    funext x
    simp only [finiteDonorThetaSource, Complex.ofReal_sub, Complex.ofReal_mul]
    ring
  rw [he, sourceTransform_add (expMomentSource_finiteDonorThetaSource m (Fin.tail γ))
    ((expMomentSource_realZeroResolvent _
      (expMomentSource_finiteDonorThetaSource m (Fin.tail γ))).const_mul _),
    sourceTransform_const_mul]
  ring

private theorem real_donor_product_ne_zero {n : ℕ} {γ : Fin n → ℝ} {t : ℝ}
    (hp : ∀ i, 0 < γ i) (ht : 0 < t) (hne : ∀ i, γ i ≠ t) :
    (∏ i, ((γ i : ℂ) ^ 2 - (t : ℂ) ^ 2)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  have hsq : γ i ^ 2 ≠ t ^ 2 := by
    intro he
    apply hne i
    nlinarith only [he, hp i, ht]
  exact sub_ne_zero.mpr (by exact_mod_cast hsq)

/-- The exact transform identity uses only the distinct actual donor zeros. -/
theorem finiteDonorThetaSource_transform (m : ℕ) {γ : Fin (m + 1) → ℝ}
    (hp : ∀ i, 0 < γ i) (hi : Function.Injective γ)
    (hz : ∀ i, XiC (γ i : ℂ) = 0) (z : ℂ) :
    sourceTransform (fun x => (finiteDonorThetaSource m γ x : ℂ)) z *
      (∏ i, ((γ i : ℂ) ^ 2 - z ^ 2)) = XiC z * (-z ^ 2 - 1 / 4) ^ m := by
  induction m generalizing z with
  | zero =>
    have hz0 : sourceTransform thetaSourceC (γ 0 : ℂ) = 0 := by
      rw [sourceTransform_thetaSourceC, hz 0]
    have h := realZeroResolvent_transform_mul (hp 0).ne' expMomentSource_thetaSourceC
      thetaCuspFullSource_neg hz0 z
    change sourceTransform (fun x => (realZeroResolvent (γ 0) thetaCuspFullSource x : ℂ)) z *
      ((γ 0 : ℂ) ^ 2 - z ^ 2) = sourceTransform thetaSourceC z at h
    rw [sourceTransform_thetaSourceC] at h
    change sourceTransform (fun x => (realZeroResolvent (γ 0) thetaCuspFullSource x : ℂ)) z *
      (∏ i : Fin 1, ((γ i : ℂ) ^ 2 - z ^ 2)) = XiC z * (-z ^ 2 - 1 / 4) ^ 0
    rw [Fin.prod_univ_one, pow_zero, mul_one]
    exact h
  | succ m ih =>
    have hpt : ∀ i, 0 < Fin.tail γ i := fun i => hp i.succ
    have hit : Function.Injective (Fin.tail γ) := hi.comp (Fin.succ_injective _)
    have hzt : ∀ i, XiC (Fin.tail γ i : ℂ) = 0 := fun i => hz i.succ
    have ht := ih hpt hit hzt z
    have hnext : sourceTransform
        (fun x => (finiteDonorThetaSource m (Fin.tail γ) x : ℂ)) (γ 0 : ℂ) = 0 := by
      have h := ih hpt hit hzt (γ 0 : ℂ)
      rw [hz 0, zero_mul] at h
      apply (mul_eq_zero.mp h).resolve_right
      apply real_donor_product_ne_zero hpt (hp 0)
      intro i he
      have hv := congrArg Fin.val (hi he)
      simp only [Fin.val_succ, Fin.val_zero] at hv
      omega
    have hr := realZeroResolvent_transform_mul (hp 0).ne'
      (expMomentSource_finiteDonorThetaSource m (Fin.tail γ))
      (finiteDonorThetaSource_even m (Fin.tail γ)) hnext z
    rw [sourceTransform_finiteDonorThetaSource_succ, Fin.prod_univ_succ]
    have hprod : (∏ i : Fin (m + 1), ((γ i.succ : ℂ) ^ 2 - z ^ 2)) =
        ∏ i : Fin (m + 1), ((Fin.tail γ i : ℂ) ^ 2 - z ^ 2) := rfl
    rw [hprod]
    have hq : ((γ 0 : ℂ) ^ 2 - z ^ 2) - ((γ 0 ^ 2 + 1 / 4 : ℝ) : ℂ) =
        -z ^ 2 - 1 / 4 := by push_cast; ring
    calc
      _ = (sourceTransform (fun x => (finiteDonorThetaSource m (Fin.tail γ) x : ℂ)) z *
          (((γ 0 : ℂ) ^ 2 - z ^ 2) - ((γ 0 ^ 2 + 1 / 4 : ℝ) : ℂ))) *
          (∏ i, ((Fin.tail γ i : ℂ) ^ 2 - z ^ 2)) := by
        linear_combination -((γ 0 ^ 2 + 1 / 4 : ℝ) : ℂ) *
          (∏ i, ((Fin.tail γ i : ℂ) ^ 2 - z ^ 2)) * hr
      _ = (-z ^ 2 - 1 / 4) *
          (sourceTransform (fun x => (finiteDonorThetaSource m (Fin.tail γ) x : ℂ)) z *
            (∏ i, ((Fin.tail γ i : ℂ) ^ 2 - z ^ 2))) := by rw [hq]; ring
      _ = _ := by rw [ht, pow_succ]; ring

/-- Actual donor cancellation makes the even Green solutions smooth through the origin. -/
theorem smooth_finiteDonorThetaSource (m : ℕ) {γ : Fin (m + 1) → ℝ}
    (hp : ∀ i, 0 < γ i) (hi : Function.Injective γ)
    (hz : ∀ i, XiC (γ i : ℂ) = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (finiteDonorThetaSource m γ x : ℂ)) := by
  induction m with
  | zero =>
    have hz0 : sourceTransform thetaSourceC (γ 0 : ℂ) = 0 := by
      rw [sourceTransform_thetaSourceC, hz 0]
    exact smooth_realZeroResolvent _ expMomentSource_thetaSourceC thetaCuspFullSource_neg
      contDiff_thetaSourceC hz0
  | succ m ih =>
    have hpt : ∀ i, 0 < Fin.tail γ i := fun i => hp i.succ
    have hit : Function.Injective (Fin.tail γ) := hi.comp (Fin.succ_injective _)
    have hzt : ∀ i, XiC (Fin.tail γ i : ℂ) = 0 := fun i => hz i.succ
    have hnext : sourceTransform
        (fun x => (finiteDonorThetaSource m (Fin.tail γ) x : ℂ)) (γ 0 : ℂ) = 0 := by
      have h := finiteDonorThetaSource_transform m hpt hit hzt (γ 0 : ℂ)
      rw [hz 0, zero_mul] at h
      apply (mul_eq_zero.mp h).resolve_right
      apply real_donor_product_ne_zero hpt (hp 0)
      intro i he
      have hv := congrArg Fin.val (hi he)
      simp only [Fin.val_succ, Fin.val_zero] at hv
      omega
    have hu := ih hpt hit hzt
    have hd := smooth_realZeroResolvent _
      (expMomentSource_finiteDonorThetaSource m (Fin.tail γ))
      (finiteDonorThetaSource_even m (Fin.tail γ)) hu hnext
    simpa only [finiteDonorThetaSource, Complex.ofReal_sub, Complex.ofReal_mul] using
      hu.sub (contDiff_const.mul hd)

/-- No inverse donor gaps enter the source bound: each additional factor costs only `O(L)`. -/
theorem finiteDonorThetaSource_uniform_bound (m : ℕ) {L : ℝ} (hL : 1 ≤ L)
    {γ : Fin (m + 1) → ℝ} (hγ : ∀ i, L ≤ γ i ∧ γ i ≤ 2 * L) (x : ℝ) :
    |finiteDonorThetaSource m γ x| ≤
      (realZeroDivisionConstant / L * ((1 + 5 * realZeroDivisionConstant) * L) ^ m) *
        thetaCuspFullSource x := by
  let B := realZeroDivisionConstant
  let R := 1 + 5 * B
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one one_le_realZeroDivisionConstant
  have hR : 0 < R := by dsimp only [R]; positivity
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  change |finiteDonorThetaSource m γ x| ≤ (B / L * (R * L) ^ m) * thetaCuspFullSource x
  induction m generalizing x with
  | zero =>
    have hg : 0 < γ 0 := hL0.trans_le (hγ 0).1
    have h := realZeroResolvent_bound hg expMomentSource_thetaSourceC (by norm_num : (0 : ℝ) ≤ 1)
      (fun t => by rw [abs_of_pos (thetaCuspFullSource_pos t), one_mul]) x
    have hd := div_le_div_of_nonneg_left hB.le hL0 (hγ 0).1
    simp only [mul_one] at h
    simpa only [finiteDonorThetaSource, pow_zero, mul_one] using
      h.trans (mul_le_mul_of_nonneg_right hd (thetaCuspFullSource_pos x).le)
  | succ m ih =>
    let u := finiteDonorThetaSource m (Fin.tail γ)
    let C := B / L * (R * L) ^ m
    let a := γ 0 ^ 2 + 1 / 4
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    have ha : 0 ≤ a := by dsimp only [a]; positivity
    have hg : 0 < γ 0 := hL0.trans_le (hγ 0).1
    have hu (t : ℝ) : |u t| ≤ C * thetaCuspFullSource t :=
      ih (γ := Fin.tail γ) (fun i => hγ i.succ) t
    have hD : |realZeroResolvent (γ 0) u x| ≤ B * C / γ 0 * thetaCuspFullSource x :=
      realZeroResolvent_bound hg (expMomentSource_finiteDonorThetaSource m (Fin.tail γ))
        hC hu x
    have haL : a ≤ 5 * L ^ 2 := by
      have hs := pow_le_pow_left₀ hg.le (hγ 0).2 2
      have hLsq : 1 ≤ L ^ 2 := by nlinarith only [hL, sq_nonneg (L - 1)]
      dsimp only [a]
      nlinarith only [hs, hLsq]
    have hcost : C + a * (B * C / γ 0) ≤ C * (R * L) := by
      calc
        _ ≤ C + a * (B * C / L) := add_le_add le_rfl
          (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left (mul_nonneg hB.le hC) hL0 (hγ 0).1) ha)
        _ ≤ C + (5 * L ^ 2) * (B * C / L) := add_le_add le_rfl
          (mul_le_mul_of_nonneg_right haL (div_nonneg (mul_nonneg hB.le hC) hL0.le))
        _ = C * (1 + 5 * B * L) := by field_simp
        _ ≤ C * (R * L) := mul_le_mul_of_nonneg_left (by dsimp only [R]; nlinarith only [hL]) hC
    change |u x - a * realZeroResolvent (γ 0) u x| ≤ _
    calc
      _ ≤ |u x| + |a * realZeroResolvent (γ 0) u x| := abs_sub _ _
      _ = |u x| + a * |realZeroResolvent (γ 0) u x| := by rw [abs_mul, abs_of_nonneg ha]
      _ ≤ C * thetaCuspFullSource x + a * (B * C / γ 0 * thetaCuspFullSource x) :=
        add_le_add (hu x) (mul_le_mul_of_nonneg_left hD ha)
      _ = (C + a * (B * C / γ 0)) * thetaCuspFullSource x := by ring
      _ ≤ (C * (R * L)) * thetaCuspFullSource x :=
        mul_le_mul_of_nonneg_right hcost (thetaCuspFullSource_pos x).le
      _ = _ := by dsimp only [C]; rw [pow_succ]; ring

end GaloisForLFunctions.ArithmeticPositiveDuality

#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.finiteDonorThetaSource_transform
#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.finiteDonorThetaSource_uniform_bound
