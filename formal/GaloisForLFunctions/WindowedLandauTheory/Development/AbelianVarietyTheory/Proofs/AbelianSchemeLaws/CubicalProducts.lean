import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeValueLaws
import Mathlib.Tactic.LinearCombination

/-! Products of cubical values along successive additions obey the torsion translation law. -/

namespace GlobalTheory.AbLaw.Cube

variable {G U : Type} [CommGroup G] [CommGroup U]

/-- Multiply cubical values along n additions by the point m. -/
def cubicalProduct (θ : G → G → G → U) (n : ℕ) (a m x : G) : U :=
  ∏ i ∈ Finset.range n, θ (a * m ^ i) m x

variable {θ : G → G → G → U} (h : IsCubicalCocycle θ)
include h

private theorem compatible_products (a b x y : G) :
    θ (a * b) x y * θ a b y * θ a b x = θ a b (x * y) * θ a x y * θ b x y := by
  have h₁ := h.cocycle a b x y
  have h₂ := h.cocycle b x y a
  rw [h.swapLast b x a, h.swapFirst b a x, h.swapFirst b (x * y) a, h.swapLast (x * y) b a,
    ← h.swapFirst a (x * y) b, h.swapLast a (x * y) b, h.swapLast x y a, h.swapFirst x a y] at h₂
  rw [h.swapFirst a (b * x) y, h.swapLast (b * x) a y] at h₁
  calc
    _ = θ (b * x) y a * θ b x y * θ a b x := by rw [h₁]
    _ = θ (b * x) y a * (θ a b x * θ b x y) := by ac_rfl
    _ = θ a b (x * y) * θ a x y * θ b x y := by rw [← mul_assoc, h₂]

private theorem cubicalProduct_add (n : ℕ) (a m x y : G) :
    cubicalProduct θ n a m (x * y) * θ a x y * θ m x y ^ n =
      θ (a * m ^ n) x y * cubicalProduct θ n a m x * cubicalProduct θ n a m y := by
  induction n with
  | zero => simp [cubicalProduct]
  | succ n ih =>
    have hc := compatible_products h (a * m ^ n) m x y
    unfold cubicalProduct at ih ⊢
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, pow_succ, pow_succ,
      ← mul_assoc a]
    apply Additive.ofMul.injective
    have e₁ := congrArg Additive.ofMul ih
    have e₂ := congrArg Additive.ofMul hc
    simp only [ofMul_mul] at e₁ e₂ ⊢
    linear_combination (norm := abel) e₁ - e₂

private theorem interchange (a b c d x : G) :
    θ (a * b) (c * d) x * θ a b x * θ c d x =
      θ (a * c) (b * d) x * θ a c x * θ b d x := by
  have e₁ := h.cocycle a b (c * d) x
  have e₂ := h.cocycle b c d x
  have e₃ := h.cocycle c b d x
  have e₄ := h.cocycle a c (b * d) x
  rw [mul_comm c b, h.swapFirst c b] at e₃
  rw [mul_left_comm c b d] at e₄
  apply Additive.ofMul.injective
  have c₁ := congrArg Additive.ofMul e₁
  have c₂ := congrArg Additive.ofMul e₂
  have c₃ := congrArg Additive.ofMul e₃
  have c₄ := congrArg Additive.ofMul e₄
  simp only [ofMul_mul] at c₁ c₂ c₃ c₄ ⊢
  linear_combination (norm := abel) c₁ - c₂ + c₃ - c₄

private theorem cubicalProduct_mul (n : ℕ) (a b x : G) :
    cubicalProduct θ n 1 (a * b) x * θ a b x ^ n =
      θ (a ^ n) (b ^ n) x * cubicalProduct θ n 1 a x * cubicalProduct θ n 1 b x := by
  induction n with
  | zero => simp [cubicalProduct, h.face]
  | succ n ih =>
    have hc := interchange h (a ^ n) (b ^ n) a b x
    simp only [cubicalProduct, Finset.prod_range_succ, one_mul] at ih ⊢
    rw [pow_succ a, pow_succ b, pow_succ (θ a b x), mul_pow a b n]
    apply Additive.ofMul.injective
    have e₁ := congrArg Additive.ofMul ih
    have e₂ := congrArg Additive.ofMul hc
    simp only [ofMul_mul] at e₁ e₂ ⊢
    linear_combination (norm := abel) e₁ + e₂

/-- Translating the multiplication product by an n-torsion point contributes
only the cubical products with that torsion point. -/
theorem cubicalProduct_translate_of_pow_eq_one (n : ℕ) (y w x : G) (hy : y ^ n = 1) :
    cubicalProduct θ n 1 (y * w) x * cubicalProduct θ n 1 y w =
      cubicalProduct θ n 1 w x * cubicalProduct θ n 1 y (x * w) := by
  have ha := cubicalProduct_mul h n y w x
  have hb := cubicalProduct_add h n 1 y x w
  rw [hy, h.face, one_mul] at ha
  rw [hy, mul_one (1 : G), h.face, one_mul, mul_one, h.swapLast y x w] at hb
  apply Additive.ofMul.injective
  have e₁ := congrArg Additive.ofMul ha
  have e₂ := congrArg Additive.ofMul hb
  simp only [ofMul_mul] at e₁ e₂ ⊢
  linear_combination (norm := abel) e₁ - e₂

end GlobalTheory.AbLaw.Cube
