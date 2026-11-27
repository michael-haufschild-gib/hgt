import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerAdditiveScale
import GaloisForLFunctions.HTGeometry.AddCharFinset

/-! Fourier coefficients on a column recover the value at zero. Invariance
under a translation forces the frequencies in the support to annihilate
that translation, and a change of columns acts contragrediently. -/

noncomputable section
open Matrix RHTower.Sieve GaloisForLFunctions.HTGeometry
open scoped Classical

namespace GlobalTheory.GLq

variable {g k : ℕ} [Fact g.Prime]

local notation "Col" => (Fin k → ZMod g)

/-- The coefficient of a frequency in the additive Fourier expansion on a column. -/
def columnFourier (ψ : AddChar (ZMod g) ℂ) (f : Col → ℂ) (ξ : Col) : ℂ :=
  ((g : ℂ) ^ k)⁻¹ * ∑ v : Col, f v * ψ (-(ξ ⬝ᵥ v))

private theorem sum_column_character (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (v : Col) :
    (∑ ξ : Col, ψ (ξ ⬝ᵥ v)) = if v = 0 then (g : ℂ) ^ k else 0 := by
  obtain ⟨c, hc⟩ := exists_addChar_scale ψ hψ
  let w : Col := fun i => (c : ZMod g) * v i
  have he (ξ : Col) : ψ (ξ ⬝ᵥ v) = finiteProductCharacter g k ξ w := by
    rw [hc]
    unfold dotProduct finiteProductCharacter
    rw [Finset.mul_sum, addChar_map_finsetSum]
    refine Finset.prod_congr rfl fun j _ => congrArg ZMod.stdAddChar ?_
    dsimp only [w]
    ring
  have hw : w = 0 ↔ v = 0 := by
    constructor
    · intro h
      funext i
      exact (mul_eq_zero.mp (congrFun h i)).resolve_left (Units.ne_zero c)
    · intro h
      subst v
      funext i
      simp [w]
  simp only [he, sum_finiteProductCharacter, hw]

/-- Summing all frequencies recovers the column function at the zero vector. -/
theorem columnFourier_sum (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (f : Col → ℂ) :
    (∑ ξ : Col, columnFourier ψ f ξ) = f 0 := by
  unfold columnFourier
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← dotProduct_neg, sum_column_character ψ hψ, neg_eq_zero]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ 0)]
  · rw [if_pos rfl, mul_left_comm, inv_mul_cancel₀, mul_one]
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero)
  · intro v _ hv
    rw [if_neg hv, mul_zero]

/-- Translating a column function multiplies each Fourier coefficient by its phase. -/
theorem columnFourier_translate (ψ : AddChar (ZMod g) ℂ) (f : Col → ℂ) (ξ z : Col) :
    columnFourier ψ (fun v => f (z + v)) ξ = ψ (ξ ⬝ᵥ z) * columnFourier ψ f ξ := by
  unfold columnFourier
  rw [mul_left_comm (ψ (ξ ⬝ᵥ z)) (((g : ℂ) ^ k)⁻¹)]
  congr 1
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft z) _ _ fun v => ?_
  change f (z + v) * ψ (-(ξ ⬝ᵥ v)) = ψ (ξ ⬝ᵥ z) * (f (z + v) * ψ (-(ξ ⬝ᵥ (z + v))))
  rw [mul_left_comm, ← AddChar.map_add_eq_mul, dotProduct_add]
  congr 2
  abel

/-- Fourier inversion on the additive group of columns. -/
theorem columnFourier_eval (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (f : Col → ℂ) (z : Col) :
    (∑ ξ : Col, columnFourier ψ f ξ * ψ (ξ ⬝ᵥ z)) = f z := by
  calc
    _ = ∑ ξ : Col, columnFourier ψ (fun v => f (z + v)) ξ :=
      Finset.sum_congr rfl fun ξ _ => by rw [columnFourier_translate, mul_comm]
    _ = _ := (columnFourier_sum ψ hψ (fun v => f (z + v))).trans (congrArg f (add_zero z))

/-- A Fourier coefficient of a translation-invariant function can be
nonzero only when its frequency annihilates the translation. -/
theorem dot_eq_zero_of_columnFourier_ne_zero (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1)
    (f : Col → ℂ) (ξ z : Col) (hz : ∀ v, f (z + v) = f v)
    (hξ : columnFourier ψ f ξ ≠ 0) : ξ ⬝ᵥ z = 0 := by
  have he := columnFourier_translate ψ f ξ z
  rw [funext hz] at he
  have hp : ψ (ξ ⬝ᵥ z) = 1 := mul_right_cancel₀ hξ (he.symm.trans (one_mul _).symm)
  obtain ⟨c, hc⟩ := exists_addChar_scale ψ hψ
  rw [hc, ← AddChar.map_zero_eq_one (ZMod.stdAddChar : AddChar (ZMod g) ℂ)] at hp
  exact (mul_eq_zero.mp (ZMod.injective_stdAddChar hp)).resolve_left (Units.ne_zero c)

/-- A matrix acting on column arguments acts by its inverse transpose on the frequencies. -/
theorem columnFourier_mulVec (ψ : AddChar (ZMod g) ℂ) (f : Col → ℂ)
    (A : Gn g k) (ξ : Col) :
    columnFourier ψ (fun v => f (A.val.mulVec v)) ξ =
      columnFourier ψ f (ξ ᵥ* A.inv) := by
  let e : Col ≃ Col := ⟨A.val.mulVec, A.inv.mulVec,
    fun v => by rw [Matrix.mulVec_mulVec, A.inv_val, Matrix.one_mulVec],
    fun v => by rw [Matrix.mulVec_mulVec, A.val_inv, Matrix.one_mulVec]⟩
  unfold columnFourier
  congr 1
  refine Fintype.sum_equiv e _ _ fun v => ?_
  change f (A.val.mulVec v) * ψ (-(ξ ⬝ᵥ v)) =
    f (A.val.mulVec v) * ψ (-((ξ ᵥ* A.inv) ⬝ᵥ A.val.mulVec v))
  rw [dotProduct_mulVec, vecMul_vecMul, A.inv_val, vecMul_one]

end GlobalTheory.GLq
