import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-!
# Complementary powers in a truncated polynomial module

On `M[x]/xᴺM[x]`, multiplication by `xᵃ` has image equal to the kernel of
multiplication by `xᵇ` whenever `N = a + b`. Coefficient shifts give explicit
preimages over any coefficient ring and for any coefficient module.

For `a = 1`, these are the alternating maps in the periodic resolution of a
truncated polynomial algebra, as in Proposition 6.4 of Ait Mohamed–El-Baz,
*Dual reflection groups of graded Ore extensions*.
-/

namespace GaloisForLFunctions.RepresentationLifting

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Multiplication by a monomial, with coefficients beyond the horizon discarded. -/
def truncatedShift (N k : ℕ) : Module.End R (Fin N → M) where
  toFun v i := if _h : k ≤ i.val then v ⟨i.val - k, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
    else 0
  map_add' v w := by
    funext i
    dsimp
    split <;> simp only [add_zero]
  map_smul' r v := by
    funext i
    dsimp
    split <;> simp only [smul_zero]

/-- Removing the first `k` coefficients gives a canonical preimage on the shift's image. -/
def truncatedDeshift (N k : ℕ) : Module.End R (Fin N → M) where
  toFun v i := if h : i.val + k < N then v ⟨i.val + k, h⟩ else 0
  map_add' v w := by
    funext i
    dsimp
    split <;> simp only [add_zero]
  map_smul' r v := by
    funext i
    dsimp
    split <;> simp only [smul_zero]

theorem truncatedShift_apply (N k : ℕ) (v : Fin N → M) (i : Fin N) :
    truncatedShift (R := R) N k v i =
      if _h : k ≤ i.val then v ⟨i.val - k, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
      else 0 := rfl

@[simp] theorem truncatedShift_zero (N : ℕ) :
    truncatedShift (R := R) (M := M) N 0 = 1 := by
  apply LinearMap.ext
  intro v
  funext i
  simp [truncatedShift]

/-- Composition adds exponents, including when their sum crosses the horizon. -/
theorem truncatedShift_mul (N a b : ℕ) :
    truncatedShift (R := R) (M := M) N a * truncatedShift N b =
      truncatedShift N (a + b) := by
  apply LinearMap.ext
  intro v
  funext i
  change truncatedShift (R := R) N a (truncatedShift (R := R) N b v) i = truncatedShift (R := R) N (a + b) v i
  simp only [truncatedShift_apply]
  by_cases ha : a ≤ i.val
  · simp only [dif_pos ha]
    by_cases hb : b ≤ i.val - a
    · rw [dif_pos hb, dif_pos (by omega)]
      congr 1
      apply Fin.ext
      change i.val - a - b = i.val - (a + b)
      omega
    · rw [dif_neg hb, dif_neg (by omega)]
  · rw [dif_neg ha, dif_neg (by omega)]

theorem truncatedShift_pow (N k : ℕ) :
    truncatedShift (R := R) (M := M) N 1 ^ k = truncatedShift N k := by
  induction k with
  | zero => exact (truncatedShift_zero N).symm
  | succ k ih => rw [pow_succ, ih, truncatedShift_mul]

@[simp] theorem truncatedShift_horizon (N : ℕ) :
    truncatedShift (R := R) (M := M) N N = 0 := by
  apply LinearMap.ext
  intro v
  funext i
  exact dif_neg (Nat.not_le.mpr i.isLt)

/-- A shifted vector vanishes exactly when its surviving input coefficients vanish. -/
theorem truncatedShift_eq_zero_iff (N k : ℕ) (v : Fin N → M) :
    truncatedShift (R := R) N k v = 0 ↔
      ∀ i : Fin N, i.val + k < N → v i = 0 := by
  constructor
  · intro h i hi
    have h' := congrFun h (⟨i.val + k, hi⟩ : Fin N)
    simpa only [truncatedShift_apply, dif_pos (Nat.le_add_left k i.val),
      Nat.add_sub_cancel, Pi.zero_apply] using h'
  · intro h
    funext i
    rw [truncatedShift_apply]
    split
    · rename_i hi
      exact h _ (by change i.val - k + k < N; omega)
    · rfl

/-- Precisely the vectors with their first `k` coefficients zero are divisible by `xᵏ`. -/
theorem mem_range_truncatedShift_iff (N k : ℕ) (v : Fin N → M) :
    v ∈ LinearMap.range (truncatedShift (R := R) N k) ↔
      ∀ i : Fin N, i.val < k → v i = 0 := by
  constructor
  · rintro ⟨w, rfl⟩ i hi
    exact dif_neg (Nat.not_le.mpr hi)
  · intro h
    refine ⟨truncatedDeshift (R := R) N k v, ?_⟩
    funext i
    rw [truncatedShift_apply]
    split
    · rename_i hi
      simp only [truncatedDeshift, LinearMap.coe_mk, AddHom.coe_mk]
      rw [dif_pos (by omega)]
      congr 1
      apply Fin.ext
      change i.val - k + k = i.val
      omega
    · exact (h i (by omega)).symm

/-- Complementary powers give exactness over arbitrary coefficient modules. -/
theorem truncatedShift_range_eq_ker (a b : ℕ) :
    LinearMap.range (truncatedShift (R := R) (M := M) (a + b) a) =
      LinearMap.ker (truncatedShift (a + b) b) := by
  ext v
  rw [mem_range_truncatedShift_iff, LinearMap.mem_ker, truncatedShift_eq_zero_iff]
  constructor <;> intro h i hi <;> exact h i (by omega)

/-- Consecutive maps of the two-periodic resolution compose to zero. -/
theorem truncatedShift_complementary_mul (a b : ℕ) :
    truncatedShift (R := R) (M := M) (a + b) a * truncatedShift (a + b) b = 0 := by
  rw [truncatedShift_mul, truncatedShift_horizon]

/-- The socle is the image of the highest nonzero monomial. -/
theorem truncatedShift_socle (n : ℕ) :
    LinearMap.ker (truncatedShift (R := R) (M := M) (n + 1) 1) =
      LinearMap.range (truncatedShift (n + 1) 1 ^ n) := by
  rw [truncatedShift_pow]
  exact (truncatedShift_range_eq_ker n 1).symm

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.truncatedShift_range_eq_ker
#print axioms GaloisForLFunctions.RepresentationLifting.truncatedShift_socle
