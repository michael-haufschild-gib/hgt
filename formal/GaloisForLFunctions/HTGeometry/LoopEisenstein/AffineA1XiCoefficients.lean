import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1Roots
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic.Linarith

/-!
# Completed-zeta coefficients for affine A₁ over ℚ

Garland's `ξ` is `completedRiemannZeta`. The coefficient attached to an affine
Weyl element is the product of `ξ(z) / ξ(z + 1)` over its inversion roots.
Exponential coordinates cover the full Godement chamber. Euler-product
nonvanishing proves that every numerator and denominator there is nonzero.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1

noncomputable section

/-- A coordinate on the entire half-plane `Re s > 1`. -/
def chamberCoordinate (z : ℂ) : ℂ := ⟨1 + Real.exp z.re, z.im⟩

theorem chamberCoordinate_re_gt_one (z : ℂ) : 1 < (chamberCoordinate z).re := by
  exact lt_add_of_pos_right 1 (Real.exp_pos z.re)

/-- Exponential coordinates cover, without restricting, the Godement half-plane. -/
theorem range_chamberCoordinate :
    Set.range chamberCoordinate = {s : ℂ | 1 < s.re} := by
  ext s
  constructor
  · rintro ⟨z, rfl⟩
    exact chamberCoordinate_re_gt_one z
  · intro hs
    refine ⟨⟨Real.log (s.re - 1), s.im⟩, ?_⟩
    apply Complex.ext
    · change 1 + Real.exp (Real.log (s.re - 1)) = s.re
      rw [Real.exp_log (sub_pos.mpr hs)]
      ring
    · rfl

/-- The two values on the simple coroots, with no assumed analytic input. -/
def godementParameter (p : ℂ × ℂ) : ℂ × ℂ :=
  (chamberCoordinate p.1, chamberCoordinate p.2)

theorem range_godementParameter :
    Set.range godementParameter = {lam : ℂ × ℂ | 1 < lam.1.re ∧ 1 < lam.2.re} := by
  ext lam
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨chamberCoordinate_re_gt_one p.1, chamberCoordinate_re_gt_one p.2⟩
  · rintro ⟨h₀, h₁⟩
    have h₀' : lam.1 ∈ Set.range chamberCoordinate := by
      rw [range_chamberCoordinate]
      exact h₀
    have h₁' : lam.2 ∈ Set.range chamberCoordinate := by
      rw [range_chamberCoordinate]
      exact h₁
    obtain ⟨z₀, hz₀⟩ := h₀'
    obtain ⟨z₁, hz₁⟩ := h₁'
    exact ⟨(z₀, z₁), Prod.ext hz₀ hz₁⟩

/-- Pairing with the actual affine coroot, including its central coordinate. -/
def rootArgument (lam : ℂ × ℂ) (β : Root) : ℂ :=
  (β.corootZero : ℂ) * lam.1 + (β.corootOne : ℂ) * lam.2

/-- The simple-root minimum bounds every positive affine-coroot argument. -/
theorem rootArgument_re_ge_min (p : ℂ × ℂ) (w : Weyl) :
    ∀ β ∈ inversions w,
      min (chamberCoordinate p.1).re (chamberCoordinate p.2).re ≤
        (rootArgument (godementParameter p) β).re := by
  intro β hβ
  have hp := ((mem_inversions w β).mp hβ).1
  have h₀ := chamberCoordinate_re_gt_one p.1
  have h₁ := chamberCoordinate_re_gt_one p.2
  have hsum : 0 ≤ (chamberCoordinate p.1).re + (chamberCoordinate p.2).re := by
    linarith only [h₀, h₁]
  cases β with
  | plus n =>
    change 0 ≤ n at hp
    have hn : (0 : ℝ) ≤ n := by exact_mod_cast hp
    have hm := mul_nonneg hn hsum
    simp only [rootArgument, godementParameter, Root.corootZero, Root.corootOne,
      Int.cast_add, Int.cast_one, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.intCast_re, Complex.intCast_im, Complex.one_re, Complex.one_im,
      zero_add, zero_mul, sub_zero] at ⊢
    nlinarith only [hm, min_le_right (chamberCoordinate p.1).re (chamberCoordinate p.2).re]
  | minus n =>
    have hn : (1 : ℝ) ≤ n := by
      have hn' : (1 : ℤ) ≤ n := by change 0 < n at hp; omega
      exact_mod_cast hn'
    have hm := mul_nonneg (sub_nonneg.mpr hn) hsum
    simp only [rootArgument, godementParameter, Root.corootZero, Root.corootOne,
      Int.cast_sub, Int.cast_one, Complex.add_re, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.intCast_re, Complex.intCast_im, Complex.one_re, Complex.one_im,
      sub_zero, zero_mul] at ⊢
    nlinarith only [hm, min_le_left (chamberCoordinate p.1).re (chamberCoordinate p.2).re]

/-- Every inversion argument lies in the Euler-product half-plane. -/
theorem rootArgument_re_gt_one (p : ℂ × ℂ) (w : Weyl) :
    ∀ β ∈ inversions w, 1 < (rootArgument (godementParameter p) β).re := by
  intro β hβ
  exact lt_of_lt_of_le
    (lt_min (chamberCoordinate_re_gt_one p.1) (chamberCoordinate_re_gt_one p.2))
    (rootArgument_re_ge_min p w β hβ)

/-- The rational rank-one intertwining factor, in Garland's ξ normalization. -/
def xiRatio (s : ℂ) : ℂ := completedRiemannZeta s / completedRiemannZeta (s + 1)

/-- The finite Gindikin–Karpelevich product for an affine Weyl element. -/
def xiCoefficient (lam : ℂ × ℂ) (w : Weyl) : ℂ :=
  ∏ β ∈ inversions w, xiRatio (rootArgument lam β)

/-- The literal product of completed zeta functions in the denominator. -/
def xiDenominator (lam : ℂ × ℂ) (w : Weyl) : ℂ :=
  ∏ β ∈ inversions w, completedRiemannZeta (rootArgument lam β + 1)

/-- The corresponding completed-zeta numerator. -/
def xiNumerator (lam : ℂ × ℂ) (w : Weyl) : ℂ :=
  ∏ β ∈ inversions w, completedRiemannZeta (rootArgument lam β)

theorem xiCoefficient_eq_div (lam : ℂ × ℂ) (w : Weyl) :
    xiCoefficient lam w = xiNumerator lam w / xiDenominator lam w := by
  exact Finset.prod_div_distrib _ _

/-- Euler-product nonvanishing also excludes zeros of the completed function. -/
theorem completedZeta_ne_zero_right {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro hz
    have he := congrArg Complex.re hz
    simp only [Complex.zero_re] at he
    linarith only [hs, he]
  intro hz
  have he := riemannZeta_def_of_ne_zero hs0
  rw [hz, zero_div] at he
  exact riemannZeta_ne_zero_of_one_lt_re hs he

/-- Every ξ denominator is nonzero throughout the full Godement chamber. -/
theorem xiDenominator_ne_zero (p : ℂ × ℂ) (w : Weyl) :
    xiDenominator (godementParameter p) w ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro β hβ
  apply completedZeta_ne_zero_right
  have h := rootArgument_re_gt_one p w β hβ
  simpa only [Complex.add_re, Complex.one_re] using (lt_trans h (lt_add_one _))

theorem xiNumerator_ne_zero (p : ℂ × ℂ) (w : Weyl) :
    xiNumerator (godementParameter p) w ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro β hβ
  exact completedZeta_ne_zero_right (rootArgument_re_gt_one p w β hβ)

theorem xiCoefficient_ne_zero (p : ℂ × ℂ) (w : Weyl) :
    xiCoefficient (godementParameter p) w ≠ 0 := by
  rw [xiCoefficient_eq_div]
  exact div_ne_zero (xiNumerator_ne_zero p w) (xiDenominator_ne_zero p w)

/-- Clearing the proved nonzero denominator recovers the numerator exactly. -/
theorem xiCoefficient_mul_denominator (p : ℂ × ℂ) (w : Weyl) :
    xiCoefficient (godementParameter p) w * xiDenominator (godementParameter p) w =
      xiNumerator (godementParameter p) w := by
  rw [xiCoefficient_eq_div, div_mul_cancel₀ _ (xiDenominator_ne_zero p w)]

@[simp] theorem xiCoefficient_one (lam : ℂ × ℂ) : xiCoefficient lam 1 = 1 := by
  simp only [xiCoefficient, inversions_one, Finset.prod_empty]

/-- The finite simple root contributes the ordinary rank-one ξ quotient. -/
@[simp] theorem xiCoefficient_finiteReflection (lam : ℂ × ℂ) :
    xiCoefficient lam finiteReflection = xiRatio lam.2 := by
  simp only [xiCoefficient, inversions_finiteReflection, Finset.prod_singleton,
    rootArgument, Root.corootZero, Root.corootOne, Int.cast_zero, zero_add,
    Int.cast_one, zero_mul, one_mul]

/-- The second simple root contributes its independent affine ξ denominator. -/
@[simp] theorem xiCoefficient_affineReflection (lam : ℂ × ℂ) :
    xiCoefficient lam affineReflection = xiRatio lam.1 := by
  simp only [xiCoefficient, inversions_affineReflection, Finset.prod_singleton,
    rootArgument, Root.corootZero, Root.corootOne, sub_self, Int.cast_one,
    Int.cast_zero, one_mul, zero_mul, add_zero]

private theorem rootStrings_disjoint (s t : Finset ℤ) :
    Disjoint (s.image Root.plus) (t.image Root.minus) := by
  apply Finset.disjoint_left.mpr
  intro β hplus hminus
  obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hplus
  obtain ⟨n, _, he⟩ := Finset.mem_image.mp hminus
  exact Root.minus_ne_plus n m he

private theorem prod_rootStrings (s t : Finset ℤ) (f : Root → ℂ) :
    (∏ β ∈ s.image Root.plus ∪ t.image Root.minus, f β) =
      (∏ n ∈ s, f (.plus n)) * ∏ n ∈ t, f (.minus n) := by
  rw [Finset.prod_union (rootStrings_disjoint s t),
    Finset.prod_image (fun _ _ _ _ h => Root.plus.inj h),
    Finset.prod_image (fun _ _ _ _ h => Root.minus.inj h)]

private theorem card_rootStrings (s t : Finset ℤ) :
    (s.image Root.plus ∪ t.image Root.minus).card = s.card + t.card := by
  rw [Finset.card_union_of_disjoint (rootStrings_disjoint s t),
    Finset.card_image_of_injective _ (fun _ _ h => Root.plus.inj h),
    Finset.card_image_of_injective _ (fun _ _ h => Root.minus.inj h)]

/-- An integral translation has exactly twice its translation distance many inversions. -/
theorem inversions_translation_card (m : ℤ) :
    (inversions (.r m)).card = (2 * m).natAbs := by
  change ((Finset.Ico 0 (2 * m)).image Root.plus ∪
    (Finset.Ioc 0 (-2 * m)).image Root.minus).card = _
  rw [card_rootStrings, Int.card_Ico, Int.card_Ioc, sub_zero, sub_zero,
    neg_mul, Int.toNat_add_toNat_neg_eq_natAbs]

/-- Reflection lengths are the odd integers in the translation coordinate. -/
theorem inversions_reflection_card (m : ℤ) :
    (inversions (.sr m)).card = (2 * m + 1).natAbs := by
  change ((Finset.Icc 0 (2 * m)).image Root.plus ∪
    (Finset.Ioo 0 (-2 * m)).image Root.minus).card = _
  rw [card_rootStrings, Int.card_Icc, Int.card_Ioo, sub_zero, sub_zero,
    show -2 * m - 1 = -(2 * m + 1) by ring,
    Int.toNat_add_toNat_neg_eq_natAbs]

/-- Exact ξ product for every integral affine translation. -/
theorem xiCoefficient_translation (lam : ℂ × ℂ) (m : ℤ) :
    xiCoefficient lam (.r m) =
      (∏ n ∈ Finset.Ico 0 (2 * m),
        xiRatio ((n : ℂ) * lam.1 + ((n : ℂ) + 1) * lam.2)) *
      ∏ n ∈ Finset.Ioc 0 (-2 * m),
        xiRatio ((n : ℂ) * lam.1 + ((n : ℂ) - 1) * lam.2) := by
  change (∏ β ∈ (Finset.Ico 0 (2 * m)).image Root.plus ∪
    (Finset.Ioc 0 (-2 * m)).image Root.minus, xiRatio (rootArgument lam β)) = _
  rw [prod_rootStrings]
  simp only [rootArgument, Root.corootZero, Root.corootOne,
    Int.cast_add, Int.cast_sub, Int.cast_one]

/-- Exact ξ product for every affine reflection, including both simple reflections. -/
theorem xiCoefficient_reflection (lam : ℂ × ℂ) (m : ℤ) :
    xiCoefficient lam (.sr m) =
      (∏ n ∈ Finset.Icc 0 (2 * m),
        xiRatio ((n : ℂ) * lam.1 + ((n : ℂ) + 1) * lam.2)) *
      ∏ n ∈ Finset.Ioo 0 (-2 * m),
        xiRatio ((n : ℂ) * lam.1 + ((n : ℂ) - 1) * lam.2) := by
  change (∏ β ∈ (Finset.Icc 0 (2 * m)).image Root.plus ∪
    (Finset.Ioo 0 (-2 * m)).image Root.minus, xiRatio (rootArgument lam β)) = _
  rw [prod_rootStrings]
  simp only [rootArgument, Root.corootZero, Root.corootOne,
    Int.cast_add, Int.cast_sub, Int.cast_one]

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1
