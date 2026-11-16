import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Five directions for ternary cubic coefficients

The nine coordinates of the level-three Schrödinger representation are
indexed by the affine plane over `𝔽₃`. A balanced triple has the form
`(a, a + v, a - v)`. Translation-invariant symmetric cubic coefficients
are therefore determined by an even function of `v`. Its five parameters
are the zero vector and the four projective directions.

This is the coefficient mechanism behind the five invariant cubics in
Section 2.3 of *A locally complete family of Kummer type hyperkähler
fourfolds*, https://arxiv.org/abs/2611.16593.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.TernaryCubic

abbrev Plane := ZMod 3 × ZMod 3
abbrev Direction := Option (Option (ZMod 3))

/-- Zero, the vertical direction, and the three finite slopes. -/
def direction (v : Plane) : Direction :=
  if v.1 = 0 then (if v.2 = 0 then none else some none) else some (some (v.2 / v.1))

def representative : Direction → Plane
  | none => (0, 0)
  | some none => (0, 1)
  | some (some t) => (1, t)

theorem direction_representative (d : Direction) : direction (representative d) = d := by
  rcases d with _ | (_ | t) <;> simp [direction, representative]

theorem direction_neg (v : Plane) : direction (-v) = direction v := by
  simp only [direction, Prod.fst_neg, Prod.snd_neg, neg_eq_zero, neg_div_neg_eq]

private theorem nonzero_eq_one_or_neg_one (x : ZMod 3) (hx : x ≠ 0) :
    x = 1 ∨ x = -1 := by
  exact sq_eq_one_iff.mp (ZMod.pow_card_sub_one_eq_one hx)

/-- A direction has precisely the two opposite representatives, except at zero. -/
theorem eq_representative_or_neg (v : Plane) :
    v = representative (direction v) ∨ v = -representative (direction v) := by
  rcases v with ⟨x, y⟩
  by_cases hx : x = 0
  · subst x
    by_cases hy : y = 0
    · subst y
      exact Or.inl (by simp [direction, representative])
    · rcases nonzero_eq_one_or_neg_one y hy with hy' | hy'
      · subst y
        exact Or.inl (by simp [direction, representative])
      · subst y
        exact Or.inr (by simp [direction, representative])
  · rcases nonzero_eq_one_or_neg_one x hx with hx' | hx'
    · subst x
      exact Or.inl (by simp [direction, representative])
    · subst x
      exact Or.inr (by simp [direction, representative, div_neg])

/-- Direction equality is exactly equality up to sign. -/
theorem direction_eq_iff (v w : Plane) : direction v = direction w ↔ v = w ∨ v = -w := by
  constructor
  · intro h
    have hv := eq_representative_or_neg v
    have hw := eq_representative_or_neg w
    rw [h] at hv
    rcases hv with hv | hv <;> rcases hw with hw | hw
    · exact Or.inl (hv.trans hw.symm)
    · exact Or.inr (by rw [hw, neg_neg]; exact hv)
    · exact Or.inr (by rw [hw]; exact hv)
    · exact Or.inl (hv.trans hw.symm)
  · rintro (rfl | rfl)
    · rfl
    · exact direction_neg w

variable (K : Type*) [Field K]

/-- Coefficient functions unchanged by negating their ternary direction. -/
def evenFunctions : Submodule K (Plane → K) where
  carrier := {f | ∀ v, f (-v) = f v}
  zero_mem' _ := rfl
  add_mem' hf hg v := congrArg₂ (· + ·) (hf v) (hg v)
  smul_mem' c _ hf v := congrArg (c • ·) (hf v)

/-- Even functions on the nine-point plane have exactly five free coordinates. -/
def evenDirectionEquiv : evenFunctions K ≃ₗ[K] (Direction → K) where
  toFun f d := f.val (representative d)
  invFun g := ⟨fun v => g (direction v), fun v => congrArg g (direction_neg v)⟩
  left_inv f := by
    apply Subtype.ext
    funext v
    rcases eq_representative_or_neg v with hv | hv
    · exact congrArg f.val hv.symm
    · exact ((congrArg f.val hv).trans (f.property _)).symm
  right_inv g := by
    funext d
    exact congrArg g (direction_representative d)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evenFunctions_finrank : Module.finrank K (evenFunctions K) = 5 := by
  rw [(evenDirectionEquiv K).finrank_eq, Module.finrank_fintype_fun_eq_card]
  simp [Direction]

theorem triple_self (a : Plane) : a + a + a = 0 := by
  have h : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
  ext <;> dsimp
  · calc a.1 + a.1 + a.1 = 3 * a.1 := by ring
         _ = 0 := by rw [h, zero_mul]
  · calc a.2 + a.2 + a.2 = 3 * a.2 := by ring
         _ = 0 := by rw [h, zero_mul]

/-- Balanced triples are affine lines, allowing the degenerate constant triple. -/
theorem balanced_triple_iff (a b c : Plane) :
    a + b + c = 0 ↔ ∃ v, b = a + v ∧ c = a - v := by
  constructor
  · intro h
    refine ⟨b - a, by abel, ?_⟩
    have h3 := triple_self a
    linear_combination h - h3
  · rintro ⟨v, rfl, rfl⟩
    calc a + (a + v) + (a - v) = a + a + a := by abel
         _ = 0 := triple_self a

/-- Symmetric cubic arrays fixed by simultaneous translations and supported
on balanced triples. The support condition is precisely phase invariance. -/
def cubicCoefficients : Submodule K (Plane → Plane → Plane → K) where
  carrier := {T |
    (∀ a b c, a + b + c ≠ 0 → T a b c = 0) ∧
    (∀ t a b c, T (a + t) (b + t) (c + t) = T a b c) ∧
    (∀ a b c, T b a c = T a b c) ∧
    (∀ a b c, T a c b = T a b c)}
  zero_mem' := ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  add_mem' h g := by
    refine ⟨fun a b c hn => ?_, fun t a b c => ?_, fun a b c => ?_, fun a b c => ?_⟩
    · exact (congrArg₂ (· + ·) (h.1 a b c hn) (g.1 a b c hn)).trans (add_zero 0)
    · exact congrArg₂ (· + ·) (h.2.1 t a b c) (g.2.1 t a b c)
    · exact congrArg₂ (· + ·) (h.2.2.1 a b c) (g.2.2.1 a b c)
    · exact congrArg₂ (· + ·) (h.2.2.2 a b c) (g.2.2.2 a b c)
  smul_mem' r _ h := by
    refine ⟨fun a b c hn => ?_, fun t a b c => ?_, fun a b c => ?_, fun a b c => ?_⟩
    · exact (congrArg (r • ·) (h.1 a b c hn)).trans (smul_zero r)
    · exact congrArg (r • ·) (h.2.1 t a b c)
    · exact congrArg (r • ·) (h.2.2.1 a b c)
    · exact congrArg (r • ·) (h.2.2.2 a b c)

private theorem translated_balance (t a b c : Plane) :
    (a + t) + (b + t) + (c + t) = a + b + c := by
  calc _ = (a + b + c) + (t + t + t) := by abel
       _ = _ := by rw [triple_self, add_zero]

private theorem balanced_difference (a b c : Plane) (h : a + b + c = 0) :
    c - a = -(b - a) := by
  have h3 := triple_self a
  linear_combination h - h3

/-- Extend an even direction function to every ordered triple. -/
def coefficientsOfEven (f : evenFunctions K) : cubicCoefficients K := by
  refine ⟨fun a b c => if a + b + c = 0 then f.val (b - a) else 0, ?_⟩
  refine ⟨fun a b c h => if_neg h, ?_, ?_, ?_⟩
  · intro t a b c
    dsimp only
    rw [translated_balance]
    have hd : (b + t) - (a + t) = b - a := by abel
    rw [hd]
  · intro a b c
    dsimp only
    have he : b + a + c = a + b + c := by abel
    rw [he]
    split_ifs
    · rw [show a - b = -(b - a) by abel, f.property]
    · rfl
  · intro a b c
    dsimp only
    have he : a + c + b = a + b + c := by abel
    rw [he]
    split_ifs with h
    · rw [balanced_difference a b c h, f.property]
    · rfl

/-- Every invariant array is recovered from the line through the origin. -/
theorem cubicCoefficients_reconstruct (T : cubicCoefficients K) (a b c : Plane) :
    T.val a b c = if a + b + c = 0 then T.val 0 (b - a) (-(b - a)) else 0 := by
  split_ifs with h
  · have ht := T.property.2.1 (-a) a b c
    simp only [add_neg_cancel, ← sub_eq_add_neg] at ht
    rw [balanced_difference a b c h] at ht
    exact ht.symm
  · exact T.property.1 a b c h

/-- Restricting to a line through the origin identifies cubic invariants
with even functions on the ternary plane. -/
def cubicEvenEquiv : cubicCoefficients K ≃ₗ[K] evenFunctions K where
  toFun T := ⟨fun v => T.val 0 v (-v), fun v => by
    simp only [neg_neg]
    exact T.property.2.2.2 0 v (-v)⟩
  invFun := coefficientsOfEven K
  left_inv T := by
    apply Subtype.ext
    funext a b c
    exact (cubicCoefficients_reconstruct K T a b c).symm
  right_inv f := by
    apply Subtype.ext
    funext v
    simp [coefficientsOfEven]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The five cubic parameters arise from the zero triple and four affine-line directions. -/
def cubicDirectionEquiv : cubicCoefficients K ≃ₗ[K] (Direction → K) :=
  (cubicEvenEquiv K).trans (evenDirectionEquiv K)

theorem cubicCoefficients_finrank : Module.finrank K (cubicCoefficients K) = 5 := by
  rw [(cubicEvenEquiv K).finrank_eq, evenFunctions_finrank]

/-- The two diagonal Heisenberg phase generators impose exactly zero total weight. -/
theorem phase_invariance_iff (T : Plane → Plane → Plane → ℂ) :
    ((∀ a b c, ZMod.stdAddChar (a.1 + b.1 + c.1) * T a b c = T a b c) ∧
      (∀ a b c, ZMod.stdAddChar (a.2 + b.2 + c.2) * T a b c = T a b c)) ↔
    (∀ a b c, a + b + c ≠ 0 → T a b c = 0) := by
  constructor
  · rintro ⟨h₁, h₂⟩ a b c hn
    by_contra hT
    apply hn
    have hphase (z : ZMod 3) (h : ZMod.stdAddChar z * T a b c = T a b c) : z = 0 := by
      apply ZMod.injective_stdAddChar
      rw [AddChar.map_zero_eq_one]
      exact mul_right_cancel₀ hT (by simpa only [one_mul] using h)
    exact Prod.ext (hphase _ (h₁ a b c)) (hphase _ (h₂ a b c))
  · intro h
    constructor <;> intro a b c <;> by_cases hs : a + b + c = 0
    · have hx := congrArg Prod.fst hs
      change a.1 + b.1 + c.1 = 0 at hx
      rw [hx, AddChar.map_zero_eq_one, one_mul]
    · rw [h a b c hs, mul_zero]
    · have hx := congrArg Prod.snd hs
      change a.2 + b.2 + c.2 = 0 at hx
      rw [hx, AddChar.map_zero_eq_one, one_mul]
    · rw [h a b c hs, mul_zero]

#print axioms evenFunctions_finrank
#print axioms balanced_triple_iff
#print axioms cubicCoefficients_finrank
#print axioms phase_invariance_iff
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.TernaryCubic
